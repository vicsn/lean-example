module

public import RustExamples.Nsl.Refine

/-! # Faithfulness of the symbolic world

The ideal world gives the adversary the same responses as the symbolic world,
unless the symbolic run leaked the secret or compared it with the nonce that
the ideal world uses for the session under attack.

The argument is "identical until bad". `Faithful.Sim` says that one pure
environment behaves like another with every nonce mapped through a function
`f`, as long as the second has not reached a `Bad` state; `Sim.step` lifts this
from the four operations to a protocol step, and `Sim.run` to a run.
`ideal_sim` instantiates it: the ideal world is the symbolic world with the
secret replaced by the nonce `n` (`subst n`), and `Bad` is "`n` is one of the
recorded guesses". The two worlds may read different tapes, as long as these
differ only in the nonce of the session under attack; the counting argument
uses this to erase that nonce from the symbolic run.

`faithful_holds` concludes that the Rust property `faithful` returns `true`.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace examples.nsl

open Model

namespace Faithful

variable {S1 S2 N1 N2 Ct : Type _}

/-- `pe1` behaves like `pe2` with every nonce mapped through `f`, until `pe2`
reaches a `Bad` state. `R` relates their states. Their ciphertexts may differ
once `pe2` reaches a `Leak` state. -/
structure Sim (pe1 : PEnv S1 N1 Ct) (pe2 : PEnv S2 N2 Ct) (f : N2 → N1) (R : S1 → S2 → Prop)
    (Bad Leak : S2 → Prop) : Prop where
  nonce : ∀ {a b} k, R a b → pe1.nonce a k = f (pe2.nonce b k)
  dec : ∀ {a b} who c, R a b → pe1.dec a who c = (pe2.dec b who c).map (msgMap f)
  same : ∀ {a b} x y, R a b → Bad (pe2.same b x y).2 ∨
    ((pe1.same a (f x) (f y)).1 = (pe2.same b x y).1 ∧
      R (pe1.same a (f x) (f y)).2 (pe2.same b x y).2)
  enc : ∀ {a b} dst m, R a b → R (pe1.enc a dst (msgMap f m)).2 (pe2.enc b dst m).2 ∧
    (¬ Leak (pe2.enc b dst m).2 → (pe1.enc a dst (msgMap f m)).1 = (pe2.enc b dst m).1)
  bad_enc : ∀ {b} dst m, Bad b → Bad (pe2.enc b dst m).2

variable {pe1 : PEnv S1 N1 Ct} {pe2 : PEnv S2 N2 Ct} {f : N2 → N1} {R : S1 → S2 → Prop}
  {Bad Leak : S2 → Prop}

/-- **One step.** From related states, a step of `pe2` either reaches a `Bad`
state, or `pe1` takes the same step: the states stay related, the sessions
agree up to `f`, and the responses are equal unless `pe2` reached `Leak`. -/
theorem Sim.step (h : Sim pe1 pe2 f R Bad Leak) (lowe : Bool) {a : S1} {b : S2} (hR : R a b)
    (ss : List (Session N2)) (act : Action Ct) :
    Bad (pstep pe2 lowe b ss act).2.1 ∨
      (R (pstep pe1 lowe a (ss.map (sessMap f)) act).2.1 (pstep pe2 lowe b ss act).2.1 ∧
        (pstep pe1 lowe a (ss.map (sessMap f)) act).2.2 =
          (pstep pe2 lowe b ss act).2.2.map (sessMap f) ∧
        (¬ Leak (pstep pe2 lowe b ss act).2.1 →
          (pstep pe1 lowe a (ss.map (sessMap f)) act).1 = (pstep pe2 lowe b ss act).1)) := by
  cases act with
  | Start owner peer =>
    by_cases ho : owner = ADVERSARY
    · simp [pstep, ho, hR]
    · simp only [pstep, ho, ↓reduceIte, List.length_map, h.nonce _ hR]
      obtain ⟨hR', hc⟩ := h.enc peer (.One (pe2.nonce b ss.length) owner) hR
      exact .inr ⟨hR', by simp [sessMap], fun hl => congrArg Response.Sent (hc hl)⟩
  | Respond owner c =>
    by_cases ho : owner = ADVERSARY
    · simp [pstep, ho, hR]
    · simp only [pstep, ho, ↓reduceIte, List.length_map, h.nonce _ hR, h.dec _ _ hR]
      rcases pe2.dec b owner c with _ | (⟨na, peer⟩ | ⟨_, _, _⟩ | _) <;>
        simp only [Option.map_none, Option.map_some, msgMap]
      · exact .inr ⟨hR, trivial, fun _ => trivial⟩
      · obtain ⟨hR', hc⟩ := h.enc peer (.Two na (pe2.nonce b ss.length) owner) hR
        exact .inr ⟨hR', by simp [sessMap], fun hl => congrArg Response.Sent (hc hl)⟩
      · exact .inr ⟨hR, trivial, fun _ => trivial⟩
      · exact .inr ⟨hR, trivial, fun _ => trivial⟩
  | Deliver k c =>
    simp only [pstep, List.getElem?_map]
    rcases ss[k.val]? with _ | s
    · exact .inr ⟨hR, rfl, fun _ => rfl⟩
    simp only [Option.map_some, sessMap, h.dec _ _ hR]
    rcases s.state with _ | _ | _
    · rcases pe2.dec b s.owner c with _ | (⟨_, _⟩ | ⟨na, nb, responder⟩ | _)
      · exact .inr ⟨hR, rfl, fun _ => rfl⟩
      · exact .inr ⟨hR, rfl, fun _ => rfl⟩
      · simp only [Option.map_some, msgMap]
        by_cases hc : (pe2.same b na s.nonce).1 = true ∧ (lowe = true → responder = s.peer)
        · rcases h.same na s.nonce hR with hbad | ⟨heq, hR1⟩
          · rw [ite_eq_left hc]
            exact .inl (h.bad_enc _ _ hbad)
          · obtain ⟨hR2, hct⟩ := h.enc s.peer (.Three nb) hR1
            rw [heq, ite_eq_left hc, ite_eq_left hc]
            exact .inr ⟨hR2, by simp [List.map_set, sessMap],
              fun hl => congrArg Response.Sent (hct hl)⟩
        · rcases h.same na s.nonce hR with hbad | ⟨heq, hR1⟩
          · rw [ite_eq_right hc]
            exact .inl hbad
          · rw [heq, ite_eq_right hc, ite_eq_right hc]
            exact .inr ⟨hR1, rfl, fun _ => rfl⟩
      · exact .inr ⟨hR, rfl, fun _ => rfl⟩
    · rcases pe2.dec b s.owner c with _ | (⟨_, _⟩ | ⟨_, _, _⟩ | nb)
      · exact .inr ⟨hR, rfl, fun _ => rfl⟩
      · exact .inr ⟨hR, rfl, fun _ => rfl⟩
      · exact .inr ⟨hR, rfl, fun _ => rfl⟩
      · simp only [Option.map_some, msgMap]
        rcases h.same nb s.nonce hR with hbad | ⟨heq, hR1⟩
        · by_cases hc : (pe2.same b nb s.nonce).1 = true
          · rw [ite_eq_left hc]; exact .inl hbad
          · rw [ite_eq_right hc]; exact .inl hbad
        · rw [heq]
          by_cases hc : (pe2.same b nb s.nonce).1 = true
          · rw [ite_eq_left hc, ite_eq_left hc]
            exact .inr ⟨hR1, by simp [List.map_set, sessMap], fun _ => rfl⟩
          · rw [ite_eq_right hc, ite_eq_right hc]
            exact .inr ⟨hR1, rfl, fun _ => rfl⟩
    · exact .inr ⟨hR, rfl, fun _ => rfl⟩
/-- A property of the state that steps preserve holds at the end of a run. -/
theorem prun_mono {S N : Type _} {pe : PEnv S N Ct} {lowe : Bool} {p : S → Prop}
    (hp : ∀ st ss act, p st → p (pstep pe lowe st ss act).2.1) (st : S) (ss : List (Session N))
    (acts : List (Action Ct)) (h : p st) : p (prun pe lowe st ss acts).1 := by
  induction acts generalizing st ss with
  | nil => exact h
  | cons act acts ih => exact ih _ _ (hp st ss act h)

/-- **A run.** If `pe2`'s run ends in a state that is neither `Bad` nor `Leak`,
`pe1` gave the same responses. `Bad` and `Leak` must be preserved by steps. -/
theorem Sim.run (h : Sim pe1 pe2 f R Bad Leak) (lowe : Bool)
    (hbad : ∀ b ss act, Bad b → Bad (pstep pe2 lowe b ss act).2.1)
    (hleak : ∀ b ss act, Leak b → Leak (pstep pe2 lowe b ss act).2.1)
    {a : S1} {b : S2} (hR : R a b) (ss : List (Session N2)) (acts : List (Action Ct))
    (hb : ¬ Bad (prun pe2 lowe b ss acts).1) (hl : ¬ Leak (prun pe2 lowe b ss acts).1) :
    (prun pe1 lowe a (ss.map (sessMap f)) acts).2.2 = (prun pe2 lowe b ss acts).2.2 := by
  induction acts generalizing a b ss with
  | nil => rfl
  | cons act acts ih =>
    simp only [prun] at hb hl ⊢
    rcases h.step lowe hR ss act with hbad' | ⟨hR', hss, hr⟩
    · exact absurd (prun_mono hbad _ _ acts hbad') hb
    · rw [hss, ih hR' _ hb hl, hr (fun hl' => hl (prun_mono hleak _ _ acts hl'))]

/-! ## The ideal world simulates the symbolic one -/

variable {Seed Coins Pk Sk : Type _}

/-- What a symbolic nonce stands for when the secret is `n`. -/
def subst (n : Std.U64) : Sym → Std.U64
  | .Val v => v
  | .Secret => n

/-- The ideal state is the symbolic one with the secret replaced by `n`. -/
def Rel (n : Std.U64) (a : IdealSt Ct) (b : SymSt Ct) : Prop :=
  a.acount = b.acount ∧ a.ocount = b.ocount ∧ a.table = b.table.map (entryMap (subst n))

/-- The tapes `t1` and `t2` agree except on the nonce of session `j`, which
is `n` on `t1`. -/
def TapeRel (j : Nat) (n : Std.U64) (t1 t2 : TapeF Seed Coins) : Prop :=
  t1.seed = t2.seed ∧ t1.coins = t2.coins ∧ (∀ k, k ≠ j → t1.nonce k = t2.nonce k) ∧
    t1.nonce j = n

theorem concF_some {m : Msg Sym} {m' : Msg Std.U64} (h : concF m = some m') (n : Std.U64) :
    msgMap (subst n) m = m' := by
  unfold concF at h; split at h <;> simp_all [msgMap, subst]

/-- The ideal world on tape `t1` is the symbolic world on tape `t2` with the
secret replaced by `n`, until the symbolic world compares the secret with `n`. -/
theorem ideal_sim (F : PkeF Seed Coins Pk Sk Ct) {t1 t2 : TapeF Seed Coins} (u : TapeF Seed Coins)
    {j : Nat} {n : Std.U64} (ht : TapeRel j n t1 t2) :
    Sim (idealEnv F t1 u) (symEnv F t2 u j) (subst n) (Rel n) (fun b => n ∈ b.guesses)
      (fun b => b.leaked = true) where
  nonce k _ := by
    simp only [idealEnv, symEnv]
    split
    · subst_vars; exact ht.2.2.2
    · exact ht.2.2.1 k ‹_›
  dec who c hR := by
    simp only [idealEnv, symEnv, hR.2.2, lookupF_map]
    cases lookupF _ who c
    · cases F.decBy u who c <;> simp [msgMap]
      rename_i m; cases m <;> rfl
    · rfl
  same x y hR := by
    rcases x with x | _ <;> rcases y with y | _
    · exact .inr ⟨rfl, hR⟩
    · by_cases hx : x = n
      · exact .inl (by simp [symEnv, hx])
      · exact .inr ⟨by simp [idealEnv, symEnv, subst, hx], hR⟩
    · by_cases hy : n = y
      · exact .inl (by simp [symEnv, hy])
      · exact .inr ⟨by simp [idealEnv, symEnv, subst, hy], hR⟩
    · exact .inr ⟨by simp [idealEnv, symEnv, subst], hR⟩
  enc dst m hR := by
    obtain ⟨h1, h2, h3⟩ := hR
    simp only [idealEnv, symEnv]
    by_cases hd : dst = ADVERSARY
    · rw [ite_eq_left hd, ite_eq_left hd]
      rcases hc : concF m with _ | m'
      · exact ⟨⟨by simp [h1], h2, h3⟩, by simp⟩
      · rw [concF_some hc n]
        exact ⟨⟨by simp [h1], h2, h3⟩, fun _ => by simp [PkeF.encTo, h1, ht.1, ht.2.1]⟩
    · rw [ite_eq_right hd, ite_eq_right hd]
      exact ⟨⟨h1, by simp [h2], by simp [h2, h3, entryMap]⟩, fun _ => by simp [h2]⟩
  bad_enc dst m hb := by
    simp only [symEnv]
    split
    · split <;> exact hb
    · exact hb
variable {F : PkeF Seed Coins Pk Sk Ct} {t u : TapeF Seed Coins} {j : Nat} {lowe : Bool}

/-- A step of the symbolic world keeps every recorded guess. -/
theorem sym_guess_mono (n : Std.U64) (b : SymSt Ct) (ss : List (Session Sym)) (act : Action Ct)
    (h : n ∈ b.guesses) : n ∈ (pstep (symEnv F t u j) lowe b ss act).2.1.guesses :=
  (symEnv_step (pstep_spec _ lowe b ss act)).1.subset h

/-- A step of the symbolic world never clears `leaked`. -/
theorem sym_leak_mono (b : SymSt Ct) (ss : List (Session Sym)) (act : Action Ct)
    (h : b.leaked = true) : (pstep (symEnv F t u j) lowe b ss act).2.1.leaked = true :=
  (symEnv_step (pstep_spec _ lowe b ss act)).2.2.1 h

/-- **Faithfulness of the models.** On tapes that differ only in the nonce `n`
of session `j`, the ideal world gives the same responses as the symbolic one
with secret session `j`, unless the symbolic run leaked or compared the secret
with `n`. -/
theorem prun_faithful (F : PkeF Seed Coins Pk Sk Ct) {t1 t2 : TapeF Seed Coins}
    (u : TapeF Seed Coins) {n : Std.U64} (ht : TapeRel j n t1 t2) (lowe : Bool)
    (acts : List (Action Ct))
    (hn : n ∉ (prun (symEnv F t2 u j) lowe ⟨0, 0, [], [], false⟩ [] acts).1.guesses)
    (hl : (prun (symEnv F t2 u j) lowe ⟨0, 0, [], [], false⟩ [] acts).1.leaked ≠ true) :
    (prun (idealEnv F t1 u) lowe ⟨0, 0, []⟩ [] acts).2.2 =
      (prun (symEnv F t2 u j) lowe ⟨0, 0, [], [], false⟩ [] acts).2.2 :=
  (ideal_sim F u ht).run lowe (sym_guess_mono n) sym_leak_mono ⟨rfl, rfl, rfl⟩ [] acts hn hl

end Faithful

/-! ## The Rust property -/

variable {P T U Seed Coins Pk Sk Ct : Type _} {E : Pke P Seed Coins Pk Sk Ct}
  {TI : Tape T Seed Coins} {UI : Tape U Seed Coins}

theorem contains_loop_spec (values : Slice Std.U64) (n : Std.U64) (i : Std.Usize)
    (hi : i.val ≤ values.length) :
    contains_loop values n i ⦃ b => b = decide (n ∈ values.val.drop i.val) ⦄ := by
  unfold contains_loop
  dsimp only
  split
  · have hd := List.drop_eq_getElem_cons (by scalar_tac : i.val < values.val.length)
    have hm : values.val[i.val] ∈ values.val.drop i.val := by rw [hd]; exact List.mem_cons_self
    step
    split
    · subst_vars; simp; exact hm
    · step*
      rw [b_post, hd, ← i3_post]; clear hd
      simp_all [eq_comm]
  · rw [List.drop_eq_nil_of_le (by scalar_tac)]; simp
termination_by values.length - i.val
decreasing_by all_goals scalar_decr_tac

/-- Equal lists of responses pass `same_responses`. -/
theorem same_responses_loop_spec (hE : E.Total) (a b : Slice (Response Ct)) (i : Std.Usize)
    (h : a.val = b.val) :
    same_responses_loop E.coremarkerCopyInst E.corecmpEqInst a b i ⦃ r => r = true ⦄ := by
  unfold same_responses_loop
  dsimp only
  split
  · step as ⟨r, hr⟩
    step as ⟨r1, hr1⟩
    obtain rfl : r1 = r := by simp [hr, hr1, h]
    cases r1 <;> simp only [hE.eq_ok, decide_true, bind_ok, ↓reduceIte] <;> step*
  · simp
termination_by a.length - i.val
decreasing_by all_goals scalar_decr_tac
theorem contains_eq (values : alloc.vec.Vec Std.U64) (n : Std.U64) :
    contains (alloc.vec.Vec.deref values) n = ok (decide (n ∈ values.val)) := by
  have := eq_ok_of_spec
    (contains_loop_spec (alloc.vec.Vec.deref values) n 0#usize (by scalar_tac))
  simpa [contains] using this

theorem same_responses_self (hE : E.Total) (a b : alloc.vec.Vec (Response Ct))
    (h : a.val = b.val) :
    same_responses E.coremarkerCopyInst E.corecmpEqInst (alloc.vec.Vec.deref a)
      (alloc.vec.Vec.deref b) = ok true := by
  have hl : (alloc.vec.Vec.deref a).len = (alloc.vec.Vec.deref b).len :=
    UScalar.eq_of_val_eq (by simp [h])
  simp only [same_responses, hl, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  exact eq_ok_of_spec (same_responses_loop_spec hE _ _ 0#usize (by simp [h]))

/-- **The symbolic world is faithful.** For both protocols, the Rust property
`faithful` returns `true` (and does not panic) for every total `Pke`, total
tapes and all inputs. -/
theorem faithful_holds (hE : E.Total) (hT : TI.Total) (hU : UI.Total) (lowe : Bool) (tape : T)
    (oracle_tape : U) (actions : Slice (Action Ct)) (secret : Std.Usize) :
    faithful E TI UI lowe tape oracle_tape actions secret = ok true := by
  obtain ⟨e1, ss1, seen1, hrun1, hp1⟩ := (ideal_refines hE hT hU tape oracle_tape).run
    E.coremarkerCopyInst lowe
    { tape, adversary := ⟨tape, 0#usize, ()⟩,
      oracle := ⟨⟨oracle_tape, 0#usize, ()⟩, alloc.vec.Vec.new _⟩ }
    actions ⟨rfl, rfl, rfl, by simp [absI, IdealSt.Fits]⟩
  obtain ⟨e2, ss2, seen2, hrun2, hp2⟩ := (sym_refines hE hT hU tape oracle_tape secret).run
    E.coremarkerCopyInst lowe
    { tape, adversary := ⟨tape, 0#usize, ()⟩, oracle := ⟨oracle_tape, 0#usize, ()⟩, secret,
      table := alloc.vec.Vec.new _, guesses := alloc.vec.Vec.new _, leaked := false }
    actions ⟨rfl, rfl, rfl, rfl, by simp [absS, SymSt.Fits]⟩
  have hz : (0#usize : Std.Usize).val = 0 := rfl
  simp only [absI, absS, alloc.vec.Vec.new, alloc.vec.Vec.from_val, hz] at hp1 hp2
  have key := Faithful.prun_faithful (pkeF hE) (t1 := tapeF hT tape) (t2 := tapeF hT tape)
    (tapeF hU oracle_tape) (j := secret.val) ⟨rfl, rfl, fun _ _ => rfl, rfl⟩ lowe actions.val
  rw [hp1, hp2] at key
  simp only [faithful, IdealOracle.new, RealOracle.new, World.new, Symbolic.new, bind_ok, hrun1,
    hrun2, uncurry_apply_pair, nonce_eq hT, contains_eq]
  split
  · rfl
  · split
    · rfl
    · rename_i hl hn
      exact same_responses_self hE seen1 seen2 (key (by simpa using hn) hl)

end examples.nsl
