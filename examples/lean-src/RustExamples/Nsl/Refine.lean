module

public import RustExamples.Nsl.Lawful
public import RustExamples.Nsl.Model

/-! # The extracted code computes the model

For a total `Pke` and total tapes, the extracted `nsl.step` in each of the
three worlds returns what `pstep` computes in the matching pure environment
(`real_refines`, `ideal_refines`, `sym_refines`). `Refines.run` and
`Refines.game` lift this to `nsl.run` and `nsl.secrecy_game`.

The extracted code can fail only by overflowing a counter or a vector. Each step
adds at most one to each, so after `k` steps none exceeds `k` (`Fits`), and the
loops make at most `Usize.max` steps.
-/

@[expose] public noncomputable section

open Aeneas Aeneas.Std Result

namespace examples.nsl

open Model

/-! ## Results -/

/-- A computation that meets a spec returns a value that satisfies it. -/
theorem exists_of_spec {α : Type _} {m : Result α} {p : α → Prop} (h : m ⦃ x => p x ⦄) :
    ∃ x, m = ok x ∧ p x := by
  cases m <;> simp_all

/-- A computation whose spec pins down its value returns that value. -/
theorem eq_ok_of_spec {α : Type _} {m : Result α} {x : α} (h : m ⦃ r => r = x ⦄) : m = ok x := by
  cases m <;> simp_all

/-- If `m` followed by `f` returns, so did `m`. -/
theorem bind_eq_ok.{u, v} {α : Type u} {β : Type v} {m : Result α} {f : α → Result β} {y : β}
    (h : Std.bind m f = ok y) : ∃ x, m = ok x ∧ f x = ok y := by
  cases m <;> simp_all

/-- Two computations that start with `m` and continue alike are equal. -/
theorem bind_ext.{u, v} {α : Type u} {β : Type v} (m : Result α) {f g : α → Result β}
    (h : ∀ x, f x = g x) : Std.bind m f = Std.bind m g := by
  rw [funext h]

/-- A `Usize` from a natural number (exact below `2 ^ numBits`). -/
def natU (i : Nat) : Std.Usize := ⟨BitVec.ofNat _ i⟩

@[simp] theorem natU_val (x : Std.Usize) : natU x.val = x := by
  cases x; simp [natU, UScalar.val]

theorem natU_val_of_le {k : Nat} (h : k ≤ Usize.max) : (natU k).val = k := by
  simp only [natU, UScalar.val, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by scalar_tac)

@[simp] theorem deref_val {α : Type _} (v : alloc.vec.Vec α) :
    (alloc.vec.Vec.deref v).val = v.val := by
  simp [alloc.vec.Vec.deref]

/-- `nsl.honest`: session `k` exists and its peer is honest. -/
theorem honest_eq {N : Type _} (ss : alloc.vec.Vec (Session N)) (k : Std.Usize) :
    honest (alloc.vec.Vec.deref ss) k =
      ok (decide (∃ s, ss.val[k.val]? = some s ∧ s.peer ≠ ADVERSARY)) := by
  apply eq_ok_of_spec
  unfold honest
  dsimp only
  have hlen : (alloc.vec.Vec.deref ss).len.val = ss.val.length := by simp
  split
  · have hk : k.val < ss.val.length := by scalar_tac
    step*
    simp only [s_post, List.getElem?_eq_getElem hk]
    cases h : (ss.val[k.val].peer != ADVERSARY) <;> simp_all
  · have hk : ss.val.length ≤ k.val := by scalar_tac
    simp [List.getElem?_eq_none hk]

/-! ## Total primitives as pure functions -/

section Prims

variable {P T Seed Coins Pk Sk Ct : Type _} {E : Pke P Seed Coins Pk Sk Ct}
  {TI : Tape T Seed Coins}

/-- A total `Pke` as pure functions. -/
def pkeF (hE : E.Total) : PkeF Seed Coins Pk Sk Ct where
  keygen s := Classical.choose (hE.keygen_ok s)
  enc pk m r := Classical.choose (hE.enc_ok pk m r)
  dec sk c := Classical.choose (hE.dec_ok sk c)

theorem keygen_eq (hE : E.Total) (s : Seed) :
    E.keygen s = ok (((pkeF hE).keygen s).1, ((pkeF hE).keygen s).2) :=
  Classical.choose_spec (hE.keygen_ok s)

theorem enc_eq (hE : E.Total) (pk : Pk) (m : Msg Std.U64) (r : Coins) :
    E.enc pk m r = ok ((pkeF hE).enc pk m r) :=
  Classical.choose_spec (hE.enc_ok pk m r)

theorem dec_eq (hE : E.Total) (sk : Sk) (c : Ct) : E.dec sk c = ok ((pkeF hE).dec sk c) :=
  Classical.choose_spec (hE.dec_ok sk c)

/-- A total tape as pure functions. No session has a number above `Usize.max`,
and the nonce of such a number is fixed to 0. -/
def tapeF (hT : TI.Total) (t : T) : TapeF Seed Coins where
  seed a := Classical.choose (hT.seed_ok t a)
  coins i := Classical.choose (hT.coins_ok t (natU i))
  nonce k := if k ≤ Usize.max then Classical.choose (hT.nonce_ok t (natU k)) else 0#u64

theorem seed_eq (hT : TI.Total) (t : T) (a : Std.U8) : TI.seed t a = ok ((tapeF hT t).seed a) :=
  Classical.choose_spec (hT.seed_ok t a)

theorem coins_eq (hT : TI.Total) (t : T) (i : Std.Usize) :
    TI.coins t i = ok ((tapeF hT t).coins i.val) := by
  have key : ∀ x y, x = y → TI.coins t x = ok (Classical.choose (hT.coins_ok t y)) := by
    rintro x _ rfl; exact Classical.choose_spec (hT.coins_ok t x)
  exact key _ _ (natU_val i).symm

theorem nonce_eq (hT : TI.Total) (t : T) (k : Std.Usize) :
    TI.nonce t k = ok ((tapeF hT t).nonce k.val) := by
  have key : ∀ x y, x = y → TI.nonce t x = ok (Classical.choose (hT.nonce_ok t y)) := by
    rintro x _ rfl; exact Classical.choose_spec (hT.nonce_ok t x)
  have hk : k.val ≤ Usize.max := by scalar_tac
  simp only [tapeF, hk, ↓reduceIte]
  exact key _ _ (natU_val k).symm

theorem tapeF_seed (hT : TI.Total) {t : T} {a : Std.U8} {s : Seed} (h : TI.seed t a = ok s) :
    (tapeF hT t).seed a = s := by
  rw [seed_eq hT] at h; exact Result.ok_injective h

theorem tapeF_coins (hT : TI.Total) {t : T} {i : Nat} {c : Coins}
    (h : TI.coins t (natU i) = ok c) : (tapeF hT t).coins i = c := by
  rw [Classical.choose_spec (hT.coins_ok t (natU i))] at h; exact Result.ok_injective h

theorem tapeF_nonce (hT : TI.Total) {t : T} {k : Std.Usize} {v : Std.U64}
    (h : TI.nonce t k = ok v) : (tapeF hT t).nonce k.val = v := by
  rw [nonce_eq hT] at h; exact Result.ok_injective h

theorem tapeF_nonce_large (hT : TI.Total) (t : T) {k : Nat} (h : Usize.max < k) :
    (tapeF hT t).nonce k = 0#u64 := by
  simp [tapeF, Nat.not_le.mpr h]

end Prims

/-! ## The oracles -/

section Oracles

variable {P T U Seed Coins Pk Sk Ct : Type _} {E : Pke P Seed Coins Pk Sk Ct}
  {TI : Tape T Seed Coins} {UI : Tape U Seed Coins}

theorem RealOracle.pk_eq (hE : E.Total) (hT : TI.Total) (o : RealOracle P T) (a : Std.U8) :
    RealOracle.Insts.ExamplesNslOracle.pk E TI o a =
      ok ((pkeF hE).keygen ((tapeF hT o.tape).seed a)).1 := by
  simp only [RealOracle.Insts.ExamplesNslOracle.pk, seed_eq hT, keygen_eq hE, bind_ok]
  rfl

theorem RealOracle.dec_eq (hE : E.Total) (hT : TI.Total) (o : RealOracle P T) (who : Std.U8)
    (c : Ct) :
    RealOracle.Insts.ExamplesNslOracle.dec E TI o who c =
      ok ((pkeF hE).decBy (tapeF hT o.tape) who c) := by
  simp only [RealOracle.Insts.ExamplesNslOracle.dec, seed_eq hT, keygen_eq hE, nsl.dec_eq hE,
    PkeF.decBy, bind_ok]
  rfl

theorem RealOracle.enc_spec (hE : E.Total) (hT : TI.Total) (o : RealOracle P T) (dst : Std.U8)
    (m : Msg Std.U64) (h : o.count.val < Usize.max) :
    RealOracle.Insts.ExamplesNslOracle.enc E TI o dst m ⦃ c o' =>
      c = (pkeF hE).encTo (tapeF hT o.tape) o.count.val dst m ∧ o'.tape = o.tape ∧
      o'.count.val = o.count.val + 1 ⦄ := by
  simp only [RealOracle.Insts.ExamplesNslOracle.enc, RealOracle.pk_eq hE hT, coins_eq hT,
    enc_eq hE]
  step*
  simp_all [PkeF.encTo]

theorem lookup_loop_spec {N : Type _} (hE : E.Total) (table : Slice (Entry Ct N)) (who : Std.U8)
    (c : Ct) (i : Std.Usize) (hi : i.val ≤ table.length) :
    lookup_loop E.coremarkerCopyInst E.corecmpEqInst table who c i ⦃ r =>
      r = lookupF (table.val.drop i.val) who c ⦄ := by
  unfold lookup_loop
  simp only [hE.eq_ok]
  step*
  all_goals (try rw [List.drop_eq_getElem_cons (by scalar_tac)])
  all_goals simp_all [lookupF]
termination_by table.length - i.val
decreasing_by all_goals scalar_decr_tac

theorem lookup_eq {N : Type _} (hE : E.Total) (I : core.marker.Copy N)
    (table : alloc.vec.Vec (Entry Ct N)) (who : Std.U8) (c : Ct) :
    lookup E.coremarkerCopyInst E.corecmpEqInst I (alloc.vec.Vec.deref table) who c =
      ok (lookupF table.val who c) := by
  have := eq_ok_of_spec (lookup_loop_spec hE (alloc.vec.Vec.deref table) who c 0#usize
    (by scalar_tac))
  simpa [lookup] using this

end Oracles

/-! ## One step -/

section Step

variable {E S N Ct : Type _} (EI : Env E Ct N) (pe : PEnv S N Ct) (abs : E → S)
  (I EncOk SameOk : E → Prop)

/-- `nsl.step` computes `pstep` in any environment whose operations compute
those of `pe` on the abstract state `abs e` and keep the invariant `I`.
`EncOk` and `SameOk` are what `enc` and `same` need in order not to overflow. -/
theorem step_refines
    (hnonce : ∀ e k, I e → EI.nonce e k = ok (pe.nonce (abs e) k.val))
    (hdec : ∀ e who c, I e → EI.dec e who c = ok (pe.dec (abs e) who c))
    (hsame : ∀ e x y, I e → SameOk e → EI.same e x y ⦃ b e' =>
      pe.same (abs e) x y = (b, abs e') ∧ I e' ∧ (EncOk e → EncOk e') ⦄)
    (henc : ∀ e dst m, I e → EncOk e → EI.enc e dst m ⦃ c e' =>
      pe.enc (abs e) dst m = (c, abs e') ∧ I e' ⦄)
    (lowe : Bool) (e : E) (s : alloc.vec.Vec (Session N)) (a : Action Ct)
    (hI : I e) (hE : EncOk e) (hS : SameOk e) (hs : s.length < Usize.max) :
    nsl.step EI lowe e s a ⦃ r e' s' =>
      pstep pe lowe (abs e) s.val a = (r, abs e', s'.val) ∧ I e' ⦄ := by
  unfold nsl.step
  cases a with
  | Start o p =>
    simp only [hnonce e _ hI, bind_ok]
    split
    · simp_all [pstep]
    · step*
      simp_all [pstep]
  | Respond o m =>
    simp only [hnonce e _ hI, hdec e _ _ hI, bind_ok]
    split
    · simp_all [pstep]
    · step* <;> simp_all [pstep]
  | Deliver k m =>
    simp only [hdec e _ _ hI, bind_ok]
    split
    · have hk : s.val[k.val]? = none := by simp; scalar_tac
      simp_all [pstep]
    · have hk : k.val < s.val.length := by scalar_tac
      step* <;> simp only [pstep, List.getElem?_eq_getElem hk] <;> simp_all

end Step

/-- The environment `EI`, seen through `abs`, computes `pe`. `Inv k` is what
the proof knows about the environment after `k` steps: from it, any step
returns what `pstep` computes, and `Inv (k + 1)` holds afterwards. -/
def Refines {E S N Ct : Type _} (EI : Env E Ct N) (pe : PEnv S N Ct) (abs : E → S)
    (Inv : Nat → E → Prop) : Prop :=
  ∀ (lowe : Bool) (k : Nat) (e : E) (s : alloc.vec.Vec (Session N)) (a : Action Ct),
    k < Usize.max → Inv k e → s.length ≤ k →
    ∃ r e' s', nsl.step EI lowe e s a = ok (r, e', s') ∧
      pstep pe lowe (abs e) s.val a = (r, abs e', s'.val) ∧ Inv (k + 1) e' ∧ s'.length ≤ k + 1

/-! ## The three worlds -/

section Worlds

variable {P T U Seed Coins Pk Sk Ct : Type _} {E : Pke P Seed Coins Pk Sk Ct}
  {TI : Tape T Seed Coins} {UI : Tape U Seed Coins}

/-- `World` over `RealOracle` as an `Env`. -/
abbrev realInst (E : Pke P Seed Coins Pk Sk Ct) (TI : Tape T Seed Coins) (UI : Tape U Seed Coins) :=
  World.Insts.ExamplesNslEnvClause0_CtU64 E TI (RealOracle.Insts.ExamplesNslOracle E UI)

/-- `World` over `IdealOracle` as an `Env`. -/
abbrev idealInst (E : Pke P Seed Coins Pk Sk Ct) (TI : Tape T Seed Coins) (UI : Tape U Seed Coins) :=
  World.Insts.ExamplesNslEnvClause0_CtU64 E TI (IdealOracle.Insts.ExamplesNslOracle E UI)

/-- `Symbolic` as an `Env`. -/
abbrev symInst (E : Pke P Seed Coins Pk Sk Ct) (TI : Tape T Seed Coins) (UI : Tape U Seed Coins) :=
  Symbolic.Insts.ExamplesNslEnvClause0_CtSym E TI UI

/-- The model state of the real world. -/
def absR (e : World P T (RealOracle P U)) : RealSt :=
  ⟨e.adversary.count.val, e.oracle.count.val⟩

/-- The model state of the ideal world. -/
def absI (e : World P T (IdealOracle P U Seed Coins Pk Sk Ct)) : IdealSt Ct :=
  ⟨e.adversary.count.val, e.oracle.real.count.val, e.oracle.table.val⟩

/-- The model state of the symbolic world. -/
def absS (e : Symbolic P T U Seed Coins Pk Sk Ct) : SymSt Ct :=
  ⟨e.adversary.count.val, e.oracle.count.val, e.table.val, e.guesses.val, e.leaked⟩

/-- After `k` steps, the real world still has tapes `t` and `u`, and its
counters are at most `k`. -/
def RealInv (t : T) (u : U) (k : Nat) (e : World P T (RealOracle P U)) : Prop :=
  e.tape = t ∧ e.adversary.tape = t ∧ e.oracle.tape = u ∧ (absR e).Fits k

/-- Finishes a `Refines` proof: the invariant after the step follows from
`pstep`'s own bounds. -/
theorem Refines.of_spec {E S N : Type _} {EI : Env E Ct N} {pe : PEnv S N Ct} {abs : E → S}
    {I : E → Prop} {lowe : Bool} {e : E} {s : alloc.vec.Vec (Session N)} {a : Action Ct} {k : Nat}
    (hs : s.length ≤ k)
    (h : nsl.step EI lowe e s a ⦃ r e' s' =>
      pstep pe lowe (abs e) s.val a = (r, abs e', s'.val) ∧ I e' ⦄) :
    ∃ r e' s', nsl.step EI lowe e s a = ok (r, e', s') ∧
      pstep pe lowe (abs e) s.val a = (r, abs e', s'.val) ∧ I e' ∧
      PStep pe lowe (abs e) s.val (r, abs e', s'.val) ∧ s'.length ≤ k + 1 := by
  obtain ⟨⟨r, e', s'⟩, heq, hp, hI⟩ := exists_of_spec h
  have hps := pstep_spec pe lowe (abs e) s.val a
  rw [hp] at hps
  have := hps.sessions.2.1
  exact ⟨r, e', s', heq, hp, hI, hps, by simp only [alloc.vec.Vec.length] at *; omega⟩

theorem real_refines (hE : E.Total) (hT : TI.Total) (hU : UI.Total) (t : T) (u : U) :
    Refines (realInst E TI UI) (realEnv (pkeF hE) (tapeF hT t) (tapeF hU u)) absR
      (RealInv t u) := by
  intro lowe k e s a hk ⟨h1, h2, h3, hf⟩ hs
  obtain ⟨c1, c2⟩ := hf
  simp only [absR] at c1 c2
  have hspec := step_refines (realInst E TI UI) (realEnv (pkeF hE) (tapeF hT t) (tapeF hU u)) absR
    (fun e => e.tape = t ∧ e.adversary.tape = t ∧ e.oracle.tape = u)
    (fun e => e.adversary.count.val < Usize.max ∧ e.oracle.count.val < Usize.max)
    (fun _ => True) ?nonce ?dec ?same ?enc lowe e s a ⟨h1, h2, h3⟩ ⟨by omega, by omega⟩ trivial
    (by simp only [alloc.vec.Vec.length] at *; omega)
  · obtain ⟨r, e', s', heq, hp, hI, hps, hs'⟩ := Refines.of_spec hs hspec
    exact ⟨r, e', s', heq, hp, ⟨hI.1, hI.2.1, hI.2.2, realEnv_fits hps ⟨c1, c2⟩⟩, hs'⟩
  case nonce =>
    rintro e k ⟨rfl, -, -⟩
    simp [World.Insts.ExamplesNslEnvClause0_CtU64.nonce, nonce_eq hT, realEnv]
  case dec =>
    rintro e who c ⟨-, -, rfl⟩
    simp [World.Insts.ExamplesNslEnvClause0_CtU64.dec, RealOracle.dec_eq hE hU, realEnv]
  case same =>
    rintro e x y hI -
    simp [World.Insts.ExamplesNslEnvClause0_CtU64.same, realEnv, hI]
    exact fun a b => ⟨a, b⟩
  case enc =>
    rintro e dst m ⟨rfl, h2, rfl⟩ ⟨c1, c2⟩
    simp only [World.Insts.ExamplesNslEnvClause0_CtU64.enc]
    split
    · step with RealOracle.enc_spec hE hT
      simp_all [realEnv, absR]
    · step with RealOracle.enc_spec hE hU
      simp_all [realEnv, absR]


/-- After `k` steps, the ideal world still has tapes `t` and `u`, and its
counters and table have at most `k` entries. -/
def IdealInv (t : T) (u : U) (k : Nat) (e : World P T (IdealOracle P U Seed Coins Pk Sk Ct)) :
    Prop :=
  e.tape = t ∧ e.adversary.tape = t ∧ e.oracle.real.tape = u ∧ (absI e).Fits k

theorem ideal_refines (hE : E.Total) (hT : TI.Total) (hU : UI.Total) (t : T) (u : U) :
    Refines (idealInst E TI UI) (idealEnv (pkeF hE) (tapeF hT t) (tapeF hU u)) absI
      (IdealInv t u) := by
  intro lowe k e s a hk ⟨h1, h2, h3, hf⟩ hs
  obtain ⟨c1, c2, c3⟩ := hf
  simp only [absI] at c1 c2 c3
  have hspec := step_refines (idealInst E TI UI) (idealEnv (pkeF hE) (tapeF hT t) (tapeF hU u))
    absI (fun e => e.tape = t ∧ e.adversary.tape = t ∧ e.oracle.real.tape = u)
    (fun e => e.adversary.count.val < Usize.max ∧ e.oracle.real.count.val < Usize.max ∧
      e.oracle.table.val.length < Usize.max)
    (fun _ => True) ?nonce ?dec ?same ?enc lowe e s a ⟨h1, h2, h3⟩ ⟨by omega, by omega, by omega⟩
    trivial (by simp only [alloc.vec.Vec.length] at *; omega)
  · obtain ⟨r, e', s', heq, hp, hI, hps, hs'⟩ := Refines.of_spec hs hspec
    exact ⟨r, e', s', heq, hp, ⟨hI.1, hI.2.1, hI.2.2, idealEnv_fits hps ⟨c1, c2, c3⟩⟩, hs'⟩
  case nonce =>
    rintro e k ⟨rfl, -, -⟩
    simp [World.Insts.ExamplesNslEnvClause0_CtU64.nonce, nonce_eq hT, idealEnv]
  case dec =>
    rintro e who c ⟨-, -, rfl⟩
    simp only [World.Insts.ExamplesNslEnvClause0_CtU64.dec, IdealOracle.Insts.ExamplesNslOracle.dec,
      lookup_eq hE, RealOracle.dec_eq hE hU, bind_ok, idealEnv, absI]
    cases lookupF e.oracle.table.val who c <;> rfl
  case same =>
    rintro e x y hI -
    simp [World.Insts.ExamplesNslEnvClause0_CtU64.same, idealEnv, hI]
    exact fun a b c => ⟨a, b, c⟩
  case enc =>
    rintro e dst m ⟨rfl, h2, rfl⟩ ⟨c1, c2, c3⟩
    simp only [World.Insts.ExamplesNslEnvClause0_CtU64.enc, IdealOracle.Insts.ExamplesNslOracle.enc]
    split
    · step with RealOracle.enc_spec hE hT
      simp_all [idealEnv, absI]
    · step with RealOracle.enc_spec hE hU as ⟨res, r1, r2, r3⟩
      obtain ⟨ct, ro⟩ := res
      step*
      simp_all [idealEnv, absI]

theorem concretize_eq (m : Msg Sym) : concretize m = ok (concF m) := by
  rcases m with ⟨a, x⟩ | ⟨a, b, x⟩ | a <;> (try cases a) <;> (try cases b) <;> rfl

theorem symbolize_eq (m : Msg Std.U64) : symbolize m = ok (msgMap Sym.Val m) := by
  cases m <;> rfl

/-- After `k` steps, the symbolic world still has tapes `t` and `u` and secret
session `j`, and its counters, table and guesses have at most `k` entries. -/
def SymInv (t : T) (u : U) (j : Std.Usize) (k : Nat) (e : Symbolic P T U Seed Coins Pk Sk Ct) :
    Prop :=
  e.tape = t ∧ e.adversary.tape = t ∧ e.oracle.tape = u ∧ e.secret = j ∧ (absS e).Fits k

theorem sym_refines (hE : E.Total) (hT : TI.Total) (hU : UI.Total) (t : T) (u : U)
    (j : Std.Usize) :
    Refines (symInst E TI UI) (symEnv (pkeF hE) (tapeF hT t) (tapeF hU u) j.val) absS
      (SymInv t u j) := by
  intro lowe k e s a hk ⟨h1, h2, h3, h4, hf⟩ hs
  obtain ⟨c1, c2, c3, c4⟩ := hf
  simp only [absS] at c1 c2 c3 c4
  have hspec := step_refines (symInst E TI UI) (symEnv (pkeF hE) (tapeF hT t) (tapeF hU u) j.val)
    absS (fun e => e.tape = t ∧ e.adversary.tape = t ∧ e.oracle.tape = u ∧ e.secret = j)
    (fun e => e.adversary.count.val < Usize.max ∧ e.oracle.count.val < Usize.max ∧
      e.table.val.length < Usize.max)
    (fun e => e.guesses.val.length < Usize.max) ?nonce ?dec ?same ?enc lowe e s a
    ⟨h1, h2, h3, h4⟩ ⟨by omega, by omega, by omega⟩ (by omega)
    (by simp only [alloc.vec.Vec.length] at *; omega)
  · obtain ⟨r, e', s', heq, hp, hI, hps, hs'⟩ := Refines.of_spec hs hspec
    exact ⟨r, e', s', heq, hp,
      ⟨hI.1, hI.2.1, hI.2.2.1, hI.2.2.2, (symEnv_step hps).2.2.2 k ⟨c1, c2, c3, c4⟩⟩, hs'⟩
  case nonce =>
    rintro e k ⟨rfl, -, -, rfl⟩
    simp only [Symbolic.Insts.ExamplesNslEnvClause0_CtSym.nonce, symEnv, nonce_eq hT, bind_ok]
    split <;> split <;> first | rfl | (exfalso; scalar_tac)
  case dec =>
    rintro e who c ⟨-, -, rfl, -⟩
    simp only [Symbolic.Insts.ExamplesNslEnvClause0_CtSym.dec, lookup_eq hE,
      RealOracle.dec_eq hE hU, bind_ok, symEnv, absS]
    cases lookupF e.table.val who c
    · cases (pkeF hE).decBy (tapeF hU e.oracle.tape) who c <;> simp [symbolize_eq]
    · rfl
  case same =>
    rintro e x y hI hg
    simp only [Symbolic.Insts.ExamplesNslEnvClause0_CtSym.same]
    cases x <;> cases y <;> step* <;> simp_all [symEnv, absS]
  case enc =>
    rintro e dst m ⟨rfl, h2, rfl, rfl⟩ ⟨c1, c2, c3⟩
    simp only [Symbolic.Insts.ExamplesNslEnvClause0_CtSym.enc, concretize_eq, bind_ok]
    split
    · rcases hc : concF m with _ | m' <;> (step with RealOracle.enc_spec hE hT) <;>
        simp_all [symEnv, absS]
    · step with RealOracle.enc_spec hE hU as ⟨ct, ro, r1, r2, r3⟩
      step*
      simp_all [symEnv, absS]

end Worlds


/-! ## Runs -/

section Run

variable {E S N Ct : Type _} {EI : Env E Ct N} {pe : PEnv S N Ct} {abs : E → S}
  {Inv : Nat → E → Prop}

theorem Refines.run_loop (h : Refines EI pe abs Inv) (lowe : Bool) (actions : Slice (Action Ct))
    (e : E) (s : alloc.vec.Vec (Session N)) (seen : alloc.vec.Vec (Response Ct)) (i : Std.Usize)
    (hi : i.val ≤ actions.length) (hinv : Inv i.val e) (hs : s.length ≤ i.val)
    (hseen : seen.length = i.val) :
    nsl.run_loop EI lowe e actions s seen i ⦃ e' s' seen' =>
      abs e' = (prun pe lowe (abs e) s.val (actions.val.drop i.val)).1 ∧
      s'.val = (prun pe lowe (abs e) s.val (actions.val.drop i.val)).2.1 ∧
      seen'.val = seen.val ++ (prun pe lowe (abs e) s.val (actions.val.drop i.val)).2.2 ⦄ := by
  unfold nsl.run_loop
  dsimp only
  split
  · step
    obtain ⟨r, e', s', heq, hp, hinv', hs'⟩ := h lowe i.val e s a (by scalar_tac) hinv hs
    rw [heq]
    step*
    case hseen => simp [alloc.vec.Vec.length, seen1_post, i2_post]; exact hseen
    rw [List.drop_eq_getElem_cons (by scalar_tac)]
    simp_all [prun]
  · rw [List.drop_eq_nil_of_le (by scalar_tac)]
    simp [prun]
termination_by actions.length - i.val
decreasing_by all_goals scalar_decr_tac

/-- `nsl.run` returns what `prun` computes. -/
theorem Refines.run (h : Refines EI pe abs Inv) (I : core.marker.Copy Ct) (lowe : Bool) (e : E)
    (actions : Slice (Action Ct)) (h0 : Inv 0 e) :
    ∃ e' ss seen, nsl.run I EI lowe e actions = ok ((ss, seen), e') ∧
      prun pe lowe (abs e) [] actions.val = (abs e', ss.val, seen.val) := by
  obtain ⟨⟨e', ss, seen⟩, heq, h1, h2, h3⟩ := exists_of_spec
    (h.run_loop lowe actions e (alloc.vec.Vec.new _) (alloc.vec.Vec.new _) 0#usize (by simp)
      (by simpa using h0) (by simp) (by simp))
  refine ⟨e', ss, seen, by simp [nsl.run, heq], ?_⟩
  simp_all

end Run


/-! ## The secrecy game -/

section Game

variable {P T O Seed Coins Pk Sk Ct A S : Type _} {E : Pke P Seed Coins Pk Sk Ct}
  {TI : Tape T Seed Coins} {OI : Oracle O Pk Ct} {pe : PEnv S Std.U64 Ct}
  {abs : World P T O → S} {Inv : Nat → World P T O → Prop}

/-- The query loop of the game computes `pplay`, whatever the game does with
its result (`K`). -/
theorem Refines.play.{w} (h : Refines (World.Insts.ExamplesNslEnvClause0_CtU64 E TI OI) pe abs Inv)
    (Adv : Adversary A Pk Sk Ct) (lowe : Bool) (q : Std.Usize) {β : Type w}
    (K : A → List (Session Std.U64) → Response Ct → Result β) (n : Nat) :
    ∀ (i : Std.Usize) (adv : A) (w : World P T O) (s : alloc.vec.Vec (Session Std.U64))
      (last : Response Ct), i.val + n = q.val → Inv i.val w → s.length ≤ i.val →
      Std.bind (secrecy_game_loop1 E TI OI Adv lowe adv q w s last i)
          (fun r => K r.1 r.2.1.val r.2.2) =
        Std.bind (pplay Adv pe lowe n adv (abs w) s.val last)
          (fun r => K r.1 r.2.2.1 r.2.2.2) := by
  induction n with
  | zero =>
    intro i adv w s last hi _ _
    rw [secrecy_game_loop1]
    simp [show ¬ i < q by scalar_tac, pplay]
  | succ n ih =>
    intro i adv w s last hi hinv hs
    rw [secrecy_game_loop1]
    simp only [show i < q by scalar_tac, ↓reduceIte, pplay, Std.bind_assoc]
    apply bind_ext
    rintro ⟨action, adv1⟩
    obtain ⟨r, w', s', heq, hp, hinv', hs'⟩ := h lowe i.val w s action (by scalar_tac) hinv hs
    obtain ⟨i1, hi1, hi1v⟩ :=
      exists_of_spec (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    simp only [uncurry_apply_pair, heq, hi1, bind_ok, hp]
    exact ih i1 adv1 w' s' r (by scalar_tac) (by rw [hi1v]; exact hinv') (by rw [hi1v]; exact hs')


theorem cast_agent (x : Std.Usize) : UScalar.cast .U8 x = agentOf x.val := by
  apply UScalar.eq_of_val_eq
  rw [UScalar.cast_val_eq]
  simp only [agentOf, UScalar.val]
  rfl

/-- The first loop of the game appends the public keys of agents `agent` to 255. -/
theorem loop0_spec (oracle : O) (pkf : Std.U8 → Pk) (hpk : ∀ a, OI.pk oracle a = ok (pkf a))
    (pks : alloc.vec.Vec Pk) (agent : Std.Usize) (h1 : agent.val ≤ 256)
    (h2 : pks.length = agent.val) :
    secrecy_game_loop0 OI oracle pks agent ⦃ r =>
      r.val = pks.val ++ (List.range' agent.val (256 - agent.val)).map fun a => pkf (agentOf a) ⦄ := by
  unfold secrecy_game_loop0
  simp only [hpk]
  step*
  · simp [alloc.vec.Vec.length, pks1_post, agent1_post]; exact h2
  · rw [r_post, pks1_post, agent1_post, show 256 - agent.val = (256 - (agent.val + 1)) + 1 by
      scalar_tac, List.range'_succ]
    simp [i_post, cast_agent]
  · simp [show 256 - agent.val = 0 by scalar_tac]
termination_by 256 - agent.val
decreasing_by scalar_decr_tac

/-- The end of the game: whether the adversary's guess wins. -/
theorem finish_spec (sessions : alloc.vec.Vec (Session Std.U64)) (k : Std.Usize)
    (guess : Std.U64) (adv : A) :
    (do
      let b ← honest (alloc.vec.Vec.deref sessions) k
      if b then do
        let s ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Session Std.U64))
          sessions k
        ok (decide (s.nonce = guess), adv)
      else ok (false, adv) : Result (Bool × A)) ⦃ r =>
      r = (wins sessions.val k.val guess, adv) ⦄ := by
  unfold honest
  dsimp only
  have hlen : (alloc.vec.Vec.deref sessions).len.val = sessions.val.length := by simp
  split
  · have hk : k.val < sessions.val.length := by scalar_tac
    step*
    all_goals simp_all [wins]
  · have hk : sessions.val.length ≤ k.val := by scalar_tac
    simp [wins, List.getElem?_eq_none hk]

theorem publicKeys_length (F : PkeF Seed Coins Pk Sk Ct) (t u : TapeF Seed Coins) :
    (publicKeys F t u).length ≤ Usize.max := by
  simp [publicKeys]; scalar_tac

/-- The public keys as the vector the game builds. -/
def keysVec (F : PkeF Seed Coins Pk Sk Ct) (t u : TapeF Seed Coins) : alloc.vec.Vec Pk :=
  alloc.vec.Vec.from (publicKeys F t u) (publicKeys_length F t u)

/-- `nsl.secrecy_game` is `pgame` over `pe`, for an oracle with the public keys
of tape `u` whose world computes `pe`. -/
theorem Refines.game (h : Refines (World.Insts.ExamplesNslEnvClause0_CtU64 E TI OI) pe abs Inv)
    (hE : E.Total) (hT : TI.Total) (tape : T) (oracle : O) (u : TapeF Seed Coins)
    (hpk : ∀ a, OI.pk oracle a = ok ((pkeF hE).keygen (u.seed a)).1)
    (h0 : Inv 0 { tape, adversary := { tape, count := 0#usize, pke := () }, oracle })
    (Adv : Adversary A Pk Sk Ct) (adv : A) (lowe : Bool) (q : Std.Usize) :
    secrecy_game E TI OI Adv lowe tape oracle adv q =
      pgame Adv pe lowe (keysVec (pkeF hE) (tapeF hT tape) u)
        ((pkeF hE).keygen ((tapeF hT tape).seed ADVERSARY)).2
        (abs { tape, adversary := { tape, count := 0#usize, pke := () }, oracle }) q.val adv := by
  obtain ⟨pks0, hpks0, hv0⟩ := exists_of_spec (alloc.vec.Vec.push_spec (alloc.vec.Vec.new Pk)
    ((pkeF hE).keygen ((tapeF hT tape).seed ADVERSARY)).1 (by simp; scalar_tac))
  obtain ⟨pks1, hpks1, hv1⟩ := exists_of_spec (loop0_spec oracle _ hpk pks0 1#usize (by simp)
    (by simp [alloc.vec.Vec.length, hv0]))
  have hk : pks1 = keysVec (pkeF hE) (tapeF hT tape) u := by
    apply alloc.vec.Vec.ext; simp [hv1, hv0, keysVec, publicKeys]
  unfold secrecy_game pgame
  simp only [seed_eq hT, keygen_eq hE, bind_ok, uncurry_apply_pair, hpks0, hpks1, hk, World.new,
    RealOracle.new]
  apply bind_ext; intro adv1
  refine Eq.trans ?_ (h.play Adv lowe q (fun adv2 ss last => Std.bind (Adv.guess adv2 last)
    fun r => ok (wins ss r.1.1.val r.1.2, r.2)) q.val 0#usize adv1 _ (alloc.vec.Vec.new _)
    .Rejected (by simp) h0 (by simp))
  apply bind_ext; rintro ⟨adv2, sessions, last⟩
  simp only [uncurry_apply_pair]
  apply bind_ext; rintro ⟨⟨k, guess⟩, adv3⟩
  simp only [uncurry_apply_pair]
  exact eq_ok_of_spec (finish_spec sessions k guess adv3)

end Game

section Games

variable {P T U Seed Coins Pk Sk Ct A : Type _} {E : Pke P Seed Coins Pk Sk Ct}
  {TI : Tape T Seed Coins} {UI : Tape U Seed Coins}

/-- The real secrecy game is `pgame` over `realEnv`. -/
theorem real_game (hE : E.Total) (hT : TI.Total) (hU : UI.Total) (Adv : Adversary A Pk Sk Ct)
    (adv : A) (lowe : Bool) (q : Std.Usize) (t : T) (u : U) :
    secrecy_game E TI (RealOracle.Insts.ExamplesNslOracle E UI) Adv lowe t
        { tape := u, count := 0#usize, pke := () } adv q =
      pgame Adv (realEnv (pkeF hE) (tapeF hT t) (tapeF hU u)) lowe
        (keysVec (pkeF hE) (tapeF hT t) (tapeF hU u))
        ((pkeF hE).keygen ((tapeF hT t).seed ADVERSARY)).2 ⟨0, 0⟩ q.val adv :=
  (real_refines hE hT hU t u).game hE hT t _ (tapeF hU u) (fun a => RealOracle.pk_eq hE hU _ a)
    ⟨rfl, rfl, rfl, by simp [absR, RealSt.Fits]⟩ Adv adv lowe q

/-- The ideal secrecy game is `pgame` over `idealEnv`. -/
theorem ideal_game (hE : E.Total) (hT : TI.Total) (hU : UI.Total) (Adv : Adversary A Pk Sk Ct)
    (adv : A) (lowe : Bool) (q : Std.Usize) (t : T) (u : U) :
    secrecy_game E TI (IdealOracle.Insts.ExamplesNslOracle E UI) Adv lowe t
        { real := { tape := u, count := 0#usize, pke := () }, table := alloc.vec.Vec.new _ } adv q =
      pgame Adv (idealEnv (pkeF hE) (tapeF hT t) (tapeF hU u)) lowe
        (keysVec (pkeF hE) (tapeF hT t) (tapeF hU u))
        ((pkeF hE).keygen ((tapeF hT t).seed ADVERSARY)).2 ⟨0, 0, []⟩ q.val adv :=
  (ideal_refines hE hT hU t u).game hE hT t _ (tapeF hU u)
    (fun a => by
      simp only [IdealOracle.Insts.ExamplesNslOracle.pk]; exact RealOracle.pk_eq hE hU _ a)
    ⟨rfl, rfl, rfl, by simp [absI, IdealSt.Fits]⟩ Adv adv lowe q

end Games

end examples.nsl
