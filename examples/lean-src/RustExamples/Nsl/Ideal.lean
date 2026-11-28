module

public import RustExamples.Nsl.Probability
import RustExamples.Nsl.Secrecy
import RustExamples.Nsl.Faithful
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Secrecy in the ideal game

With Lowe's check, every adversary making `q` queries wins the ideal secrecy
game with probability at most `q (q + 1) / 2^64` (`idealWin_le`).

Fix the session `j` that the adversary names. Run the same adversary against
the symbolic world with secret session `j`, on the tape with session `j`'s
nonce erased, and collect the values it compares with the secret and its final
guess (`badList`). This list has at most `q + 1` entries and does not depend on
session `j`'s nonce.

`couple` shows that an adversary that wins the ideal game by naming session
`j` has that session's nonce in the list. The ideal and the symbolic run are
coupled step by step with `Faithful.Sim.step`: until the symbolic run compares
the secret with the nonce or leaks, the adversary sees the same responses in
both, so it is in the same state. If the symbolic run leaks, `Secrecy.Inv` says
the peer of session `j` is the adversary, so naming `j` does not win.

A uniform nonce hits a list of `q + 1` values that do not depend on it with
probability at most `(q + 1) / 2^64` (`card_lens_le`); the bound sums this over
the `q` sessions.
-/

noncomputable section

open Aeneas Aeneas.Std Result

namespace examples.nsl

open Model

/-! ## The adversary against the symbolic world -/

section Couple

variable {A Pk Sk Ct Seed Coins S N : Type _} {Adv : Adversary A Pk Sk Ct}

/-- The values that the adversary's run against a symbolic world compares
with the secret, and its final guess. The run makes `q` more queries from the
adversary state `adv` and stops early if the adversary fails. -/
def symGuesses (Adv : Adversary A Pk Sk Ct) (pe : PEnv (SymSt Ct) Sym Ct) :
    Nat → A → SymSt Ct → List (Session Sym) → Response Ct → List Std.U64
  | 0, adv, st, _, last =>
    match (Adv.guess adv last).match with
    | .ok ((_, guess), _) => guess :: st.guesses
    | _ => st.guesses
  | q + 1, adv, st, ss, last =>
    match (Adv.next adv last).match with
    | .ok (action, adv) =>
      let r := pstep pe true st ss action
      symGuesses Adv pe q adv r.2.1 r.2.2 r.1
    | _ => st.guesses

variable {F : PkeF Seed Coins Pk Sk Ct} {t u : TapeF Seed Coins} {j : Nat}

/-- `symGuesses` keeps the guesses recorded so far and adds at most one per
query, plus the final guess. -/
theorem symGuesses_spec (q : Nat) (adv : A) (st : SymSt Ct) (ss : List (Session Sym))
    (last : Response Ct) :
    (∀ x ∈ st.guesses, x ∈ symGuesses Adv (symEnv F t u j) q adv st ss last) ∧
      (symGuesses Adv (symEnv F t u j) q adv st ss last).length ≤ st.guesses.length + q + 1 := by
  induction q generalizing adv st ss last with
  | zero =>
    simp only [symGuesses]
    split
    · exact ⟨fun x hx => List.mem_cons_of_mem _ hx, by simp⟩
    · exact ⟨fun x hx => hx, by omega⟩
  | succ q ih =>
    simp only [symGuesses]
    split
    · rename_i action adv1 _
      have hstep := pstep_spec (symEnv F t u j) true st ss action
      generalize pstep (symEnv F t u j) true st ss action = r at hstep ⊢
      obtain ⟨r, st', ss'⟩ := r
      obtain ⟨hpre, hlen, -⟩ := symEnv_step hstep
      obtain ⟨ih1, ih2⟩ := ih adv1 st' ss' r
      dsimp only
      exact ⟨fun x hx => ih1 x (hpre.subset hx), by omega⟩
    · exact ⟨fun x hx => hx, by omega⟩

/-- The query loop creates at most one session per query and never changes a
session's peer. -/
theorem pplay_sessions {pe : PEnv S N Ct} {lowe : Bool} (q : Nat) (adv : A) (st : S)
    (ss : List (Session N)) (last : Response Ct) {res : A × S × List (Session N) × Response Ct}
    (h : pplay Adv pe lowe q adv st ss last = ok res) :
    res.2.2.1.length ≤ ss.length + q ∧
      ∀ (k : Nat) (s : Session N), ss[k]? = some s →
        ∃ s', res.2.2.1[k]? = some s' ∧ s'.peer = s.peer := by
  induction q generalizing adv st ss last with
  | zero =>
    simp only [pplay, Result.ok.injEq] at h
    subst h
    exact ⟨by simp, fun k s hk => ⟨s, hk, rfl⟩⟩
  | succ q ih =>
    obtain ⟨⟨action, adv1⟩, -, h⟩ := bind_eq_ok h
    have hstep := pstep_spec pe lowe st ss action
    simp only [uncurry_apply_pair] at h
    generalize pstep pe lowe st ss action = r at hstep h
    obtain ⟨r, st', ss'⟩ := r
    obtain ⟨hl1, hl2, hold, -⟩ := hstep.sessions
    obtain ⟨ih1, ih2⟩ := ih adv1 st' ss' r h
    refine ⟨by omega, fun k s hk => ?_⟩
    obtain ⟨s1, hs1, -, hp1, -⟩ := hold k s hk
    obtain ⟨s2, hs2, hp2⟩ := ih2 k s1 hs1
    exact ⟨s2, hs2, hp2.trans hp1⟩
variable {t1 t2 : TapeF Seed Coins} {n : Std.U64}

/-- **The coupling.** Run the adversary for `q` queries against the ideal
world on tape `t1` and against the symbolic world with secret session `j` on
tape `t2`, from related states. If the adversary then guesses the nonce `n` of
session `j` and wins in the ideal world, `n` is among `symGuesses`. -/
theorem couple (ht : Faithful.TapeRel j n t1 t2) (q : Nat) (adv : A) (a : IdealSt Ct)
    (b : SymSt Ct) (ss : List (Session Sym)) (last : Response Ct)
    {res : A × IdealSt Ct × List (Session Std.U64) × Response Ct} {k : Std.Usize} {g : Std.U64}
    {adv' : A} (hR : Faithful.Rel n a b) (hinv : Secrecy.Inv j b ss)
    (hsec : ∀ s, ss[j]? = some s → s.nonce = .Secret)
    (hplay : pplay Adv (idealEnv F t1 u) true q adv a (ss.map (sessMap (Faithful.subst n))) last =
      ok res)
    (hguess : Adv.guess res.1 res.2.2.2 = ok ((k, g), adv')) (hwin : wins res.2.2.1 j g = true) :
    n ∈ symGuesses Adv (symEnv F t2 u j) q adv b ss last := by
  induction q generalizing adv a b ss last with
  | zero =>
    simp only [pplay, Result.ok.injEq] at hplay
    subst hplay
    simp only [symGuesses, hguess, Result.match.ok]
    -- The session the adversary names holds the secret, which stands for `n`.
    simp only [wins, List.getElem?_map] at hwin
    rcases hs : ss[j]? with _ | s
    · simp [hs] at hwin
    · simp [hs, sessMap, hsec s hs, Faithful.subst] at hwin
      simp [hwin.2]
  | succ q ih =>
    obtain ⟨⟨action, adv1⟩, hnext, hplay⟩ := bind_eq_ok hplay
    simp only [uncurry_apply_pair] at hplay
    simp only [symGuesses, hnext, Result.match.ok]
    have hsim := (Faithful.ideal_sim F u ht).step true hR ss action
    have hstep := pstep_spec (symEnv F t2 u j) true b ss action
    generalize pstep (symEnv F t2 u j) true b ss action = r2 at hsim hstep ⊢
    obtain ⟨r2, b', ss'⟩ := r2
    generalize pstep (idealEnv F t1 u) true a (ss.map (sessMap (Faithful.subst n))) action = r1
      at hsim hplay
    obtain ⟨r1, a', ss1⟩ := r1
    dsimp only at hsim hplay ⊢
    rcases hsim with hbad | ⟨hR', rfl, hr⟩
    · -- The symbolic run compared the secret with `n`.
      exact (symGuesses_spec q adv1 b' ss' r2).1 n hbad
    have hinv' := hinv.step hstep
    have hsec' : ∀ s, ss'[j]? = some s → s.nonce = .Secret := by
      intro s hs
      obtain ⟨hl1, hl2, hold, hnew⟩ := hstep.sessions
      by_cases hj : j < ss.length
      · obtain ⟨s', hs', -, -, hn⟩ := hold j ss[j] (List.getElem?_eq_getElem hj)
        rw [hs] at hs'; cases hs'
        rw [hn]; exact hsec _ (List.getElem?_eq_getElem hj)
      · have : j = ss.length := by have := (List.getElem?_eq_some_iff.mp hs).1; omega
        subst this
        rw [hnew s hs]; simp [symEnv]
    by_cases hl : b'.leaked = true
    · -- The symbolic run leaked: the peer of session `j` is the adversary.
      exfalso
      obtain ⟨s, hs, hp⟩ := hinv'.leaked hl
      obtain ⟨s', hs', hp'⟩ := (pplay_sessions q adv1 a' _ r1 hplay).2 j
        (sessMap (Faithful.subst n) s) (by simp [hs])
      simp [wins, hs', hp', sessMap, hp] at hwin
    · rw [hr hl] at hplay
      exact ih adv1 a' b' ss' r2 hR' hinv' hsec' hplay

end Couple
namespace Game

/-! ## The ideal game on uniform tapes -/

section Bad

variable {P Seed Coins Pk Sk Ct A : Type} {E : Pke P Seed Coins Pk Sk Ct} {q : Nat}

/-- A game tape as pure functions. -/
abbrev tapeOf (t : GameTape Seed Coins q) : TapeF Seed Coins :=
  tapeF (gameTape_total Seed Coins q) t

/-- The tape `t` with session `j`'s nonce set to 0. -/
def erase (j : Fin q) (t : GameTape Seed Coins q) : GameTape Seed Coins q :=
  { t with nonces := Function.update t.nonces j 0#u64 }

/-- Erasing session `j`'s nonce changes nothing else on the tape. -/
theorem tapeRel_erase (hq : q ≤ Usize.max) (j : Fin q) (t : GameTape Seed Coins q) :
    Faithful.TapeRel j.val (t.nonces j) (tapeOf t) (tapeOf (erase j t)) := by
  have hnonce : ∀ (t : GameTape Seed Coins q) (k : Std.Usize),
      (tapeOf t).nonce k.val = if h : k.val < q then t.nonces ⟨k.val, h⟩ else 0#u64 :=
    fun t k => tapeF_nonce _ rfl
  refine ⟨?_, ?_, fun k hk => ?_, ?_⟩
  · funext a; exact (tapeF_seed _ rfl).trans (tapeF_seed _ rfl).symm
  · funext i; exact (tapeF_coins _ rfl).trans (tapeF_coins _ rfl).symm
  · by_cases hbig : k ≤ Usize.max
    · obtain ⟨k, rfl⟩ : ∃ kU : Std.Usize, kU.val = k := ⟨natU k, natU_val_of_le hbig⟩
      rw [hnonce, hnonce]
      split
      · exact (Function.update_of_ne (fun h => hk (congrArg Fin.val h)) _ _).symm
      · rfl
    · rw [tapeF_nonce_large _ _ (by omega), tapeF_nonce_large _ _ (by omega)]
  · obtain ⟨k, hk⟩ : ∃ kU : Std.Usize, kU.val = j.val := ⟨natU j.val, natU_val_of_le (by omega)⟩
    have hlt : k.val < q := by omega
    rw [← hk, hnonce]
    simp only [hlt, ↓reduceDIte]
    congr 1; exact Fin.ext hk

theorem keysVec_congr {F : PkeF Seed Coins Pk Sk Ct} {t t' : TapeF Seed Coins}
    (u : TapeF Seed Coins) (h : t.seed = t'.seed) : keysVec F t u = keysVec F t' u := by
  apply alloc.vec.Vec.ext; simp [keysVec, publicKeys, h]

/-- The values that the adversary compares with the secret, and its final
guess, when it plays the game against the symbolic world with secret session
`j` on the tapes `t` and `ot`. -/
def badList (hE : E.Total) (Adv : Adversary A Pk Sk Ct) (adv : A) (j : Nat)
    (t ot : GameTape Seed Coins q) : List Std.U64 :=
  match (Adv.start adv (keysVec (pkeF hE) (tapeOf t) (tapeOf ot))
      ((pkeF hE).keygen ((tapeOf t).seed ADVERSARY)).2).match with
  | .ok adv =>
    symGuesses Adv (symEnv (pkeF hE) (tapeOf t) (tapeOf ot) j) q adv ⟨0, 0, [], [], false⟩ []
      .Rejected
  | _ => []

/-- `badList` has at most `q + 1` entries: one per query, and the final guess. -/
theorem badList_length (hE : E.Total) (Adv : Adversary A Pk Sk Ct) (adv : A) (j : Nat)
    (t ot : GameTape Seed Coins q) : (badList hE Adv adv j t ot).length ≤ q + 1 := by
  unfold badList
  split
  · rename_i adv1 _
    have := (symGuesses_spec (Adv := Adv) (F := pkeF hE) (t := tapeOf t) (u := tapeOf ot)
      (j := j) q adv1 ⟨0, 0, [], [], false⟩ [] .Rejected).2
    simpa using this
  · simp

/-- **Winning the ideal game means hitting the bad list.** If the adversary
wins the ideal secrecy game with Lowe's check, it names a session `j` whose
nonce is in the bad list computed with that nonce erased. -/
theorem ideal_win_bad (hE : E.Total) (Adv : Adversary A Pk Sk Ct) (adv : A) (qu : Std.Usize)
    (t ot : GameTape Seed Coins qu.val) (adv' : A)
    (h : secrecy_game E (gameTape Seed Coins qu.val)
      (IdealOracle.Insts.ExamplesNslOracle E (gameTape Seed Coins qu.val)) Adv true t
      { real := { tape := ot, count := 0#usize, pke := () }, table := alloc.vec.Vec.new _ }
      adv qu = ok (true, adv')) :
    ∃ j : Fin qu.val, t.nonces j ∈ badList hE Adv adv j.val (erase j t) ot := by
  rw [ideal_game hE (gameTape_total _ _ _) (gameTape_total _ _ _)] at h
  simp only [pgame] at h
  obtain ⟨adv1, hstart, h⟩ := bind_eq_ok h
  obtain ⟨⟨adv2, st, ss, last⟩, hplay, h⟩ := bind_eq_ok h
  simp only [uncurry_apply_pair] at h
  obtain ⟨⟨⟨k, g⟩, adv3⟩, hguess, h⟩ := bind_eq_ok h
  simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨hwin, -⟩ := h
  -- The adversary names an existing session, and there are at most `q`.
  have hk : k.val < qu.val := by
    have hlen := (pplay_sessions _ _ _ _ _ hplay).1
    rcases hs : ss[k.val]? with _ | s
    · simp [wins, hs] at hwin
    · have := (List.getElem?_eq_some_iff.mp hs).1
      simp at hlen; omega
  have ht := tapeRel_erase (by scalar_tac) ⟨k.val, hk⟩ t
  refine ⟨⟨k.val, hk⟩, ?_⟩
  simp only [badList, ← ht.1, ← keysVec_congr _ ht.1, hstart, Result.match.ok]
  exact couple ht qu.val adv1 ⟨0, 0, []⟩ ⟨0, 0, [], [], false⟩ [] .Rejected ⟨rfl, rfl, rfl⟩
    Secrecy.Inv.init (by simp) hplay hguess hwin

end Bad
/-! ## Counting -/

/-- Let `get`/`set` be a lens onto a `U64` coordinate of a finite type `Ω`, and
let `L ω` be a list of at most `m` values. The coordinate lies in the list
computed from the outcome with that coordinate erased (`L (set ω z)`) for at
most `m / 2^64` of the outcomes. -/
theorem card_lens_le {Ω : Type} [Fintype Ω] [DecidableEq Ω] (z : Std.U64) (get : Ω → Std.U64)
    (set : Ω → Std.U64 → Ω) (hgs : ∀ ω m, get (set ω m) = m)
    (hss : ∀ ω m m', set (set ω m) m' = set ω m') (hsg : ∀ ω, set ω (get ω) = ω)
    (L : Ω → List Std.U64) (m : Nat) (hL : ∀ ω, (L ω).length ≤ m)
    [DecidablePred fun ω => get ω ∈ L (set ω z)] :
    (Finset.univ.filter fun ω => get ω ∈ L (set ω z)).card * 2 ^ 64 ≤ m * Fintype.card Ω := by
  classical
  let π : Ω → Ω := fun ω => set ω z
  let T := Finset.univ.image π
  have hrec : ∀ ω, set (π ω) (get ω) = ω := fun ω => by simp only [π, hss, hsg]
  have hT : ∀ x ∈ T, set x z = x := by
    intro x hx
    obtain ⟨ω, -, rfl⟩ := Finset.mem_image.mp hx
    simp only [π, hss]
  -- Each fiber of `π` has 2^64 elements.
  have hfib : ∀ x ∈ T, (Finset.univ.filter fun ω => π ω = x).card = 2 ^ 64 := by
    intro x hx
    have : (Finset.univ.filter fun ω => π ω = x) = Finset.univ.image (set x) := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro h; exact ⟨get ω, by rw [← h, hrec]⟩
      · rintro ⟨m', rfl⟩; simp only [π, hss]; exact hT x hx
    rw [this, Finset.card_image_of_injective _ (fun a b h => by
      have := congrArg get h; simpa [hgs] using this)]
    simp [card_u64]
  -- In each fiber the event has at most `m` elements.
  have hev : ∀ x ∈ T,
      ((Finset.univ.filter fun ω => get ω ∈ L (set ω z)).filter fun ω => π ω = x).card ≤ m := by
    intro x _
    calc _ ≤ (L x).toFinset.card := by
          apply Finset.card_le_card_of_injOn get
          · intro ω hω
            simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
              Set.mem_ofPred_eq] at hω
            simp only [Finset.mem_coe, List.mem_toFinset]
            rw [← hω.2]; exact hω.1
          · intro a ha b hb hab
            simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
              Set.mem_ofPred_eq] at ha hb
            rw [← hrec a, ← hrec b, ha.2, hb.2, hab]
      _ ≤ (L x).length := List.toFinset_card_le _
      _ ≤ m := hL x
  have h1 := Finset.card_eq_sum_card_fiberwise (f := π) (t := T)
    (s := Finset.univ.filter fun ω => get ω ∈ L (set ω z))
    (fun ω _ => Finset.mem_image_of_mem π (Finset.mem_univ ω))
  have h2 := Finset.card_eq_sum_card_fiberwise (f := π) (t := T) (s := Finset.univ)
    (fun ω _ => Finset.mem_image_of_mem π (Finset.mem_univ ω))
  have h3 : (Finset.univ.filter fun ω => get ω ∈ L (set ω z)).card ≤ T.card * m := by
    rw [h1]
    calc _ ≤ ∑ _x ∈ T, m := Finset.sum_le_sum hev
      _ = T.card * m := by simp
  have h4 : Fintype.card Ω = T.card * 2 ^ 64 := by
    rw [← Finset.card_univ, h2, Finset.sum_congr rfl hfib]
    simp
  rw [h4]
  calc _ ≤ T.card * m * 2 ^ 64 := Nat.mul_le_mul_right _ h3
    _ = m * (T.card * 2 ^ 64) := by ring

variable {P Seed Coins Pk Sk Ct A : Type} [Fintype Seed] [Fintype Coins]

/-- **Secrecy in the ideal game.** With Lowe's check, the adversary wins the
ideal secrecy game with probability at most `q (q + 1) / 2^64`. -/
public theorem idealWin_le {E : Pke P Seed Coins Pk Sk Ct} (hE : E.Total) (Adv : Adversary A Pk Sk Ct)
    (adv : A) (qu : Std.Usize) :
    idealWin E Adv adv true qu ≤ (qu.val * (qu.val + 1) : ℝ) / 2 ^ 64 := by
  classical
  let q := qu.val
  let Win : Outcome Seed Coins q → Prop := fun ω =>
    ∃ adv', (do
      let o ← IdealOracle.new E (gameTape Seed Coins q) ω.2
      secrecy_game E (gameTape Seed Coins q)
        (IdealOracle.Insts.ExamplesNslOracle E (gameTape Seed Coins q)) Adv true ω.1 o adv qu) =
      ok (true, adv')
  let Bad : Fin q → Outcome Seed Coins q → Prop := fun j ω =>
    ω.1.nonces j ∈ badList hE Adv adv j.val (erase j ω.1) ω.2
  -- Winning means hitting some session's bad list.
  have hsub : (Finset.univ.filter Win) ⊆
      Finset.univ.biUnion fun j => Finset.univ.filter (Bad j) := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Win, IdealOracle.new,
      RealOracle.new, bind_ok] at hω
    obtain ⟨adv', h⟩ := hω
    simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
    exact ideal_win_bad hE Adv adv qu ω.1 ω.2 adv' h
  -- Each session's bad list is hit with probability at most (q + 1) / 2^64.
  have hj : ∀ j : Fin q, (Finset.univ.filter (Bad j)).card * 2 ^ 64 ≤
      (q + 1) * Fintype.card (Outcome Seed Coins q) := fun j =>
    card_lens_le (Ω := Outcome Seed Coins q) 0#u64 (fun ω => ω.1.nonces j)
      (fun ω m => ({ ω.1 with nonces := Function.update ω.1.nonces j m }, ω.2))
      (fun ω m => by simp) (fun ω m m' => by simp) (fun ω => by simp)
      (fun ω => badList hE Adv adv j.val ω.1 ω.2) (q + 1)
      (fun ω => badList_length hE Adv adv j.val ω.1 ω.2)
  have hW : (Finset.univ.filter Win).card * 2 ^ 64 ≤
      q * (q + 1) * Fintype.card (Outcome Seed Coins q) := by
    calc (Finset.univ.filter Win).card * 2 ^ 64
        ≤ (∑ j : Fin q, (Finset.univ.filter (Bad j)).card) * 2 ^ 64 :=
          Nat.mul_le_mul_right _ ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)
      _ = ∑ j : Fin q, (Finset.univ.filter (Bad j)).card * 2 ^ 64 := Finset.sum_mul _ _ _
      _ ≤ ∑ _j : Fin q, (q + 1) * Fintype.card (Outcome Seed Coins q) :=
          Finset.sum_le_sum fun j _ => hj j
      _ = q * (q + 1) * Fintype.card (Outcome Seed Coins q) := by simp [mul_assoc]
  unfold idealWin prob
  change ((Finset.univ.filter Win).card : ℝ) / Fintype.card (Outcome Seed Coins q) ≤ _
  rcases Nat.eq_zero_or_pos (Fintype.card (Outcome Seed Coins q)) with h0 | h0
  · rw [h0]; simp; positivity
  · rw [div_le_div_iff₀ (by exact_mod_cast h0) (by positivity)]
    exact_mod_cast hW

end Game

end examples.nsl
