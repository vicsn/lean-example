module

public import RustExamples.Nsl.Refine

/-! # Symbolic secrecy of NSL

With Lowe's check, no run of the protocol in the symbolic world encrypts a
message mentioning the secret to the adversary, unless the session under
attack has the adversary as its peer.

`Secrecy.Inv` is the invariant, on the model state of the symbolic world. Let
`σ` be the index of the session whose nonce is the secret.

* Before session `σ` exists, the secret appears nowhere.
* Once it exists with an honest peer, let `a` be its initiator and `b` its
  responder. Nothing leaked, and the secret appears only in the table entries
  `Allowed a b`: the protocol's own messages between `a` and `b`.
* If its peer is the adversary, anything may happen.

`Secrecy.Inv.step` shows that every step preserves the invariant. Lowe's check
is used in one place: an initiator that accepts `{na, Secret, b}` addressed to
`a` answers `b`, and not whoever it believes it is talking to.

`secrecy_holds` concludes that the Rust property `secrecy` returns `true`.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace examples.nsl

open Model

namespace Secrecy

variable {Ct Seed Coins Pk Sk : Type _} {F : PkeF Seed Coins Pk Sk Ct} {t u : TapeF Seed Coins}
  {σ : Nat}

/-- The message does not mention the secret. -/
def msgClean : Msg Sym → Prop
  | .One a _ => a ≠ .Secret
  | .Two a b _ => a ≠ .Secret ∧ b ≠ .Secret
  | .Three a => a ≠ .Secret

/-- What a table entry may be when the session under attack runs between the
honest initiator `a` and the honest responder `b`: a message without the secret,
or one of the protocol's messages between `a` and `b` that carry it. -/
def Allowed (a b : Std.U8) (e : Entry Ct Sym) : Prop :=
  msgClean e.msg ∨
  (e.«to» = b ∧ e.msg = .One .Secret a) ∨
  (e.«to» = a ∧ ∃ nb, nb ≠ .Secret ∧ e.msg = .Two .Secret nb b) ∨
  (e.«to» = a ∧ ∃ na, na ≠ .Secret ∧ e.msg = .Two na .Secret b) ∨
  (e.«to» = b ∧ e.msg = .Three .Secret)

/-- Nothing leaked and every table entry satisfies `p`. -/
def Kept (p : Entry Ct Sym → Prop) (st : SymSt Ct) : Prop :=
  st.leaked = false ∧ ∀ e ∈ st.table, p e

/-- The secrecy invariant of the symbolic world with secret session `σ`. -/
structure Inv (σ : Nat) (st : SymSt Ct) (ss : List (Session Sym)) : Prop where
  /-- Before session `σ` exists, the secret appears nowhere. -/
  before : ss.length ≤ σ → Kept (fun e => msgClean e.msg) st
  /-- If session `σ` has an honest peer, the secret stays between two honest
  agents. -/
  honest : ∀ s, ss[σ]? = some s → s.peer ≠ ADVERSARY →
    ∃ a b, a ≠ ADVERSARY ∧ b ≠ ADVERSARY ∧ Kept (Allowed a b) st

/-! ## The operations of the symbolic world -/

theorem concF_eq_none {m : Msg Sym} (h : msgClean m) : concF m ≠ none := by
  rcases m with ⟨a, x⟩ | ⟨a, b, x⟩ | a <;> (try cases a) <;> (try cases b) <;>
    simp_all [msgClean, concF]

/-- Decryption gives a table entry addressed to the decrypting agent, or a
message without the secret. -/
theorem dec_cases {p : Entry Ct Sym → Prop} {st : SymSt Ct} {who : Std.U8} {c : Ct} {m : Msg Sym}
    (hk : Kept p st) (h : (symEnv F t u σ).dec st who c = some m) :
    (∃ e, p e ∧ e.«to» = who ∧ e.msg = m) ∨ msgClean m := by
  simp only [symEnv] at h
  split at h
  · rename_i m' hl
    obtain ⟨e, he, hto, hm⟩ := lookupF_mem hl
    cases h
    exact .inl ⟨e, hk.2 e he, hto, hm⟩
  · right
    cases hd : F.decBy u who c <;> simp [hd] at h
    subst h
    rename_i m'
    cases m' <;> simp [msgMap, msgClean]

/-- Comparing nonces changes neither the table nor `leaked`. -/
theorem Kept.same {p : Entry Ct Sym → Prop} {st : SymSt Ct} (hk : Kept p st) (x y : Sym) :
    Kept p ((symEnv F t u σ).same st x y).2 := by
  cases x <;> cases y <;> exact hk

/-- Encrypting `m` to `dst` keeps the invariant if `m` does not mention the
secret when `dst` is the adversary, and makes a good table entry otherwise. -/
theorem Kept.enc {p : Entry Ct Sym → Prop} {st : SymSt Ct} (hk : Kept p st) {dst : Std.U8}
    {m : Msg Sym} (hadv : dst = ADVERSARY → msgClean m)
    (hnew : dst ≠ ADVERSARY → ∀ ct, p { «to» := dst, ct, msg := m }) :
    Kept p ((symEnv F t u σ).enc st dst m).2 := by
  simp only [symEnv]
  split
  · rename_i hd
    have := concF_eq_none (hadv hd)
    split
    · exact hk
    · contradiction
  · rename_i hd
    refine ⟨hk.1, fun e he => ?_⟩
    simp only [List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact hk.2 e he
    · exact hnew hd _

/-- A new session gets the secret as its nonce exactly when it is session `σ`. -/
theorem nonce_clean {st : SymSt Ct} {k : Nat} (h : k ≠ σ) :
    (symEnv F t u σ).nonce st k ≠ .Secret := by
  simp [symEnv, h]

/-! ## Preservation -/

variable {st st' : SymSt Ct} {ss ss' : List (Session Sym)} {r : Response Ct}

/-- A step that does not create session `σ` keeps a table without the secret. -/
theorem clean_step (hk : Kept (fun e => msgClean e.msg) st) (hlen : ss'.length ≤ σ)
    (h : PStep (symEnv F t u σ) true st ss (r, st', ss')) :
    Kept (fun e : Entry Ct Sym => msgClean e.msg) st' := by
  have clean : ∀ {who c m}, (symEnv F t u σ).dec st who c = some m → msgClean m := by
    intro who c m hd
    rcases dec_cases hk hd with ⟨e, he, -, rfl⟩ | hm
    · exact he
    · exact hm
  cases h with
  | reject => exact hk
  | mismatch x y | responded => exact hk.same _ _
  | start owner peer =>
    have hn : (symEnv F t u σ).nonce st ss.length ≠ .Secret := nonce_clean (by simp at hlen; omega)
    exact hk.enc (fun _ => hn) (fun _ _ => hn)
  | respond owner peer c na _ hd =>
    have hn : (symEnv F t u σ).nonce st ss.length ≠ .Secret := nonce_clean (by simp at hlen; omega)
    have hm : msgClean (.Two na ((symEnv F t u σ).nonce st ss.length) owner) := ⟨clean hd, hn⟩
    exact hk.enc (fun _ => hm) (fun _ _ => hm)
  | initiated k s c na nb responder _ _ hd =>
    have hm : msgClean (.Three nb) := (clean hd).2
    exact (hk.same _ _).enc (fun _ => hm) (fun _ _ => hm)

/-- Once session `σ` exists between honest `a` and `b`, every step keeps the
secret between them. This is where Lowe's check is needed. -/
theorem safe_step {a b : Std.U8} (ha : a ≠ ADVERSARY) (hb : b ≠ ADVERSARY)
    (hk : Kept (Allowed a b) st) (hlen : σ < ss.length)
    (h : PStep (symEnv F t u σ) true st ss (r, st', ss')) : Kept (Allowed a b) st' := by
  have hn : (symEnv F t u σ).nonce st ss.length ≠ .Secret := nonce_clean (by omega)
  cases h with
  | reject => exact hk
  | mismatch x y | responded => exact hk.same _ _
  | start owner peer => exact hk.enc (fun _ => hn) (fun _ _ => .inl hn)
  | respond owner peer c na _ hd =>
    rcases dec_cases hk hd with ⟨e, he, hto, hm⟩ | hm
    · rcases he with he | ⟨h1, h2⟩ | ⟨-, _, -, h2⟩ | ⟨-, _, -, h2⟩ | ⟨-, h2⟩
      · rw [hm] at he
        exact hk.enc (fun _ => ⟨he, hn⟩) (fun _ _ => .inl ⟨he, hn⟩)
      · -- `b` answers `{Secret, a}`: the reply goes to `a`.
        rw [hm] at h2; cases h2
        rw [hto] at h1; subst h1
        exact hk.enc (fun h => absurd h ha) (fun _ _ => .inr (.inr (.inl ⟨rfl, _, hn, rfl⟩)))
      all_goals (rw [hm] at h2; cases h2)
    · exact hk.enc (fun _ => ⟨hm, hn⟩) (fun _ _ => .inl ⟨hm, hn⟩)
  | initiated k s c na nb responder _ _ hd _ hlowe =>
    have clean : nb ≠ .Secret → Kept (Allowed a b)
        ((symEnv F t u σ).enc ((symEnv F t u σ).same st na s.nonce).2 s.peer (.Three nb)).2 :=
      fun h => (hk.same _ _).enc (fun _ => h) (fun _ _ => .inl h)
    rcases dec_cases hk hd with ⟨e, he, hto, hm⟩ | hm
    · rcases he with he | ⟨-, h2⟩ | ⟨-, _, h1, h2⟩ | ⟨h1, _, -, h2⟩ | ⟨-, h2⟩
      · rw [hm] at he; exact clean he.2
      · rw [hm] at h2; cases h2
      · rw [hm] at h2; cases h2; exact clean h1
      · -- `a` accepts `{na, Secret, b}`: with Lowe's check its peer is `b`.
        rw [hm] at h2; cases h2
        rw [← hlowe rfl]
        exact (hk.same _ _).enc (fun h => absurd h hb)
          (fun _ _ => .inr (.inr (.inr (.inr ⟨rfl, rfl⟩))))
      · rw [hm] at h2; cases h2
    · exact clean hm.2
/-- The step that creates session `σ` with an honest peer starts the invariant
between its initiator and its responder. -/
theorem create_step (hk : Kept (fun e => msgClean e.msg) st) (hlen : ss.length = σ)
    (h : PStep (symEnv F t u σ) true st ss (r, st', ss')) {s' : Session Sym}
    (hs : ss'[σ]? = some s') (hp : s'.peer ≠ ADVERSARY) :
    ∃ a b, a ≠ ADVERSARY ∧ b ≠ ADVERSARY ∧ Kept (Allowed a b) st' := by
  have hsec : (symEnv F t u σ).nonce st ss.length = .Secret := by simp [symEnv, hlen]
  have hk' : ∀ a b, Kept (Allowed a b) st := fun a b => ⟨hk.1, fun e he => .inl (hk.2 e he)⟩
  subst hlen
  cases h with
  | reject | mismatch | initiated | responded => simp at hs
  | start owner peer ho =>
    obtain rfl : s' = { owner, peer, nonce := _, state := .Initiating } := by simpa using hs.symm
    rw [hsec]
    exact ⟨owner, peer, ho, hp, (hk' _ _).enc (fun h => absurd h hp)
      (fun _ _ => .inr (.inl ⟨rfl, rfl⟩))⟩
  | respond owner peer c na ho hd =>
    obtain rfl : s' = { owner, peer, nonce := _, state := .Responding } := by simpa using hs.symm
    have hna : na ≠ .Secret := by
      rcases dec_cases hk hd with ⟨e, he, -, hm⟩ | hm
      · rw [hm] at he; exact he
      · exact hm
    rw [hsec]
    exact ⟨peer, owner, hp, ho, (hk' _ _).enc (fun h => absurd h hp)
      (fun _ _ => .inr (.inr (.inr (.inl ⟨rfl, na, hna, rfl⟩))))⟩

/-- The invariant holds before the first step. -/
theorem Inv.init : Inv σ ({ acount := 0, ocount := 0, table := [], guesses := [], leaked := false } :
    SymSt Ct) [] :=
  ⟨fun _ => ⟨rfl, by simp⟩, by simp⟩

/-- **Every step with Lowe's check preserves the invariant.** -/
theorem Inv.step (hi : Inv σ st ss) (h : PStep (symEnv F t u σ) true st ss (r, st', ss')) :
    Inv σ st' ss' := by
  obtain ⟨hl1, hl2, hold, -⟩ := h.sessions
  refine ⟨fun hlen => clean_step (hi.before (by omega)) hlen h, fun s' hs hp => ?_⟩
  by_cases hσ : σ < ss.length
  · obtain ⟨s'', hs'', -, hpeer, -⟩ := hold σ ss[σ] (List.getElem?_eq_getElem hσ)
    rw [hs] at hs''; cases hs''
    obtain ⟨a, b, ha, hb, hk⟩ :=
      hi.honest ss[σ] (List.getElem?_eq_getElem hσ) (by rw [← hpeer]; exact hp)
    exact ⟨a, b, ha, hb, safe_step ha hb hk hσ h⟩
  · have : σ < ss'.length := (List.getElem?_eq_some_iff.mp hs).1
    exact create_step (hi.before (by omega)) (by omega) h hs hp

/-- A run preserves the invariant. -/
theorem Inv.prun (hi : Inv σ st ss) (acts : List (Action Ct)) :
    Inv σ (prun (symEnv F t u σ) true st ss acts).1 (prun (symEnv F t u σ) true st ss acts).2.1 := by
  induction acts generalizing st ss with
  | nil => exact hi
  | cons a acts ih => exact ih (hi.step (pstep_spec _ _ _ _ a))

/-- **A leak means the session under attack talks to the adversary.** -/
theorem Inv.leaked (hi : Inv σ st ss) (hl : st.leaked = true) :
    ∃ s, ss[σ]? = some s ∧ s.peer = ADVERSARY := by
  have hσ : σ < ss.length := by
    by_contra hc
    have := (hi.before (by omega)).1
    simp [hl] at this
  refine ⟨ss[σ], List.getElem?_eq_getElem hσ, ?_⟩
  by_contra hp
  obtain ⟨_, _, _, _, hk⟩ := hi.honest _ (List.getElem?_eq_getElem hσ) hp
  have := hk.1
  simp [hl] at this

end Secrecy

variable {P T U Seed Coins Pk Sk Ct : Type _} {E : Pke P Seed Coins Pk Sk Ct}
  {TI : Tape T Seed Coins} {UI : Tape U Seed Coins}

/-- **Symbolic secrecy of NSL.** With Lowe's check, the Rust property `secrecy`
returns `true` (and does not panic) for every total `Pke`, total tapes and all
inputs: if the symbolic run encrypts a message mentioning the secret to the
adversary, the peer of the session under attack is the adversary. -/
theorem secrecy_holds (hE : E.Total) (hT : TI.Total) (hU : UI.Total) (tape : T) (oracle_tape : U)
    (actions : Slice (Action Ct)) (secret : Std.Usize) :
    secrecy E TI UI true tape oracle_tape actions secret = ok true := by
  obtain ⟨e', ss, seen, hrun, hp⟩ := (sym_refines hE hT hU tape oracle_tape secret).run
    E.coremarkerCopyInst true
    { tape, adversary := ⟨tape, 0#usize, ()⟩, oracle := ⟨oracle_tape, 0#usize, ()⟩, secret,
      table := alloc.vec.Vec.new _, guesses := alloc.vec.Vec.new _, leaked := false }
    actions ⟨rfl, rfl, rfl, rfl, by simp [absS, SymSt.Fits]⟩
  have hinv := (Secrecy.Inv.init (σ := secret.val)).prun (F := pkeF hE) (t := tapeF hT tape)
    (u := tapeF hU oracle_tape) actions.val
  have hz : (0#usize : Std.Usize).val = 0 := rfl
  simp only [absS, alloc.vec.Vec.new, alloc.vec.Vec.from_val, hz] at hp
  rw [hp] at hinv
  simp only [secrecy, Symbolic.new, RealOracle.new, bind_ok, hrun, uncurry_apply_pair, honest_eq]
  split
  · obtain ⟨s, hs, hpeer⟩ := hinv.leaked ‹_›
    simp [hs, hpeer]
  · rfl

end examples.nsl
