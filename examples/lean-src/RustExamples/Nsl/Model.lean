module

public import RustExamples.Gen.Funs

/-! # A pure model of the NSL worlds

The extracted `nsl.step` is generic over an `Env` and returns a `Result`. Here
it is modelled once, as the total function `pstep` over a pure environment
`PEnv`. The three worlds of `examples/src/nsl.rs` are the pure environments
`realEnv`, `idealEnv` and `symEnv`, whose states keep only counters and tables;
the encryption scheme and the tapes are pure functions (`PkeF`, `TapeF`).
`prun` and `pgame` model `nsl.run` and `nsl.secrecy_game`.

`RustExamples.Nsl.Refine` shows that the extracted code computes these models.
Every other proof is about the models.
-/

@[expose] public noncomputable section

open Aeneas Aeneas.Std Result

namespace examples.nsl.Model

variable {S N M Ct Seed Coins Pk Sk A : Type _}

/-! ## Encryption and tapes as pure functions -/

/-- A `Pke` as pure functions. -/
structure PkeF (Seed Coins Pk Sk Ct : Type _) where
  keygen : Seed → Pk × Sk
  enc : Pk → Msg Std.U64 → Coins → Ct
  dec : Sk → Ct → Option (Msg Std.U64)

/-- A `Tape` as pure functions. -/
structure TapeF (Seed Coins : Type _) where
  seed : Std.U8 → Seed
  coins : Nat → Coins
  nonce : Nat → Std.U64

/-- `RealOracle.enc`: encrypts `m` to agent `dst` with the `i`-th coins of `t`. -/
def PkeF.encTo (F : PkeF Seed Coins Pk Sk Ct) (t : TapeF Seed Coins) (i : Nat) (dst : Std.U8)
    (m : Msg Std.U64) : Ct :=
  F.enc (F.keygen (t.seed dst)).1 m (t.coins i)

/-- `RealOracle.dec`: decrypts `c` with the key of agent `who`. -/
def PkeF.decBy (F : PkeF Seed Coins Pk Sk Ct) (t : TapeF Seed Coins) (who : Std.U8) (c : Ct) :
    Option (Msg Std.U64) :=
  F.dec (F.keygen (t.seed who)).2 c

/-! ## The protocol over a pure environment -/

/-- An `Env` as pure functions on a state `S`. -/
structure PEnv (S N Ct : Type _) where
  nonce : S → Nat → N
  same : S → N → N → Bool × S
  enc : S → Std.U8 → Msg N → Ct × S
  dec : S → Std.U8 → Ct → Option (Msg N)

/-- `nsl.step` over a pure environment. -/
def pstep (pe : PEnv S N Ct) (lowe : Bool) (st : S) (ss : List (Session N)) :
    Action Ct → Response Ct × S × List (Session N)
  | .Start owner peer =>
    if owner = ADVERSARY then (.Rejected, st, ss) else
      let nonce := pe.nonce st ss.length
      let sent := pe.enc st peer (.One nonce owner)
      (.Sent sent.1, sent.2, ss ++ [{ owner, peer, nonce, state := .Initiating }])
  | .Respond owner msg =>
    if owner = ADVERSARY then (.Rejected, st, ss) else
      match pe.dec st owner msg with
      | some (.One na peer) =>
        let nonce := pe.nonce st ss.length
        let sent := pe.enc st peer (.Two na nonce owner)
        (.Sent sent.1, sent.2, ss ++ [{ owner, peer, nonce, state := .Responding }])
      | _ => (.Rejected, st, ss)
  | .Deliver k msg =>
    match ss[k.val]? with
    | none => (.Rejected, st, ss)
    | some s =>
      match s.state with
      | .Initiating =>
        match pe.dec st s.owner msg with
        | some (.Two na nb responder) =>
          let same := pe.same st na s.nonce
          if same.1 = true ∧ (lowe = true → responder = s.peer) then
            let sent := pe.enc same.2 s.peer (.Three nb)
            (.Sent sent.1, sent.2, ss.set k.val { s with state := .Done })
          else (.Rejected, same.2, ss)
        | _ => (.Rejected, st, ss)
      | .Responding =>
        match pe.dec st s.owner msg with
        | some (.Three nb) =>
          let same := pe.same st nb s.nonce
          if same.1 = true then (.Accepted, same.2, ss.set k.val { s with state := .Done })
          else (.Rejected, same.2, ss)
        | _ => (.Rejected, st, ss)
      | .Done => (.Rejected, st, ss)

/-- `nsl.run` over a pure environment: the final state, the sessions and every
response. -/
def prun (pe : PEnv S N Ct) (lowe : Bool) (st : S) (ss : List (Session N)) :
    List (Action Ct) → S × List (Session N) × List (Response Ct)
  | [] => (st, ss, [])
  | a :: acts =>
    let r := pstep pe lowe st ss a
    let rest := prun pe lowe r.2.1 r.2.2 acts
    (rest.1, rest.2.1, r.1 :: rest.2.2)

/-- The query loop of `nsl.secrecy_game` over a pure environment: `q` rounds of
the adversary's `next` followed by a step. It fails only if the adversary does. -/
def pplay (Adv : Adversary A Pk Sk Ct) (pe : PEnv S N Ct) (lowe : Bool) :
    Nat → A → S → List (Session N) → Response Ct →
      Result (A × S × List (Session N) × Response Ct)
  | 0, adv, st, ss, last => ok (adv, st, ss, last)
  | q + 1, adv, st, ss, last => do
    let (action, adv) ← Adv.next adv last
    let r := pstep pe lowe st ss action
    pplay Adv pe lowe q adv r.2.1 r.2.2 r.1

/-- The adversary wins by naming session `k` and the nonce `guess`: the session
exists, its peer is honest and `guess` is its nonce. -/
def wins (ss : List (Session Std.U64)) (k : Nat) (guess : Std.U64) : Bool :=
  match ss[k]? with
  | some s => decide (s.peer ≠ ADVERSARY ∧ s.nonce = guess)
  | none => false

/-- `nsl.secrecy_game` over a pure environment with initial state `st`, given
the public keys `pks` and the adversary's secret key `sk`. -/
def pgame (Adv : Adversary A Pk Sk Ct) (pe : PEnv S Std.U64 Ct) (lowe : Bool)
    (pks : alloc.vec.Vec Pk) (sk : Sk) (st : S) (q : Nat) (adv : A) : Result (Bool × A) := do
  let adv ← Adv.start adv pks sk
  let (adv, _, ss, last) ← pplay Adv pe lowe q adv st [] .Rejected
  let ((k, guess), adv) ← Adv.guess adv last
  ok (wins ss k.val guess, adv)

/-! ## The ways a step can go -/

/-- The result of a step from state `st` and sessions `ss`. Proofs about
`pstep` go by cases on this relation instead of unfolding `pstep`. -/
inductive PStep (pe : PEnv S N Ct) (lowe : Bool) (st : S) (ss : List (Session N)) :
    Response Ct × S × List (Session N) → Prop
  /-- The action is rejected before any nonce comparison. -/
  | reject : PStep pe lowe st ss (.Rejected, st, ss)
  /-- The action is rejected after comparing `x` and `y`. -/
  | mismatch (x y : N) : PStep pe lowe st ss (.Rejected, (pe.same st x y).2, ss)
  /-- `owner` starts a session with `peer`. -/
  | start (owner peer : Std.U8) : owner ≠ ADVERSARY →
      PStep pe lowe st ss
        (.Sent (pe.enc st peer (.One (pe.nonce st ss.length) owner)).1,
          (pe.enc st peer (.One (pe.nonce st ss.length) owner)).2,
          ss ++ [{ owner, peer, nonce := pe.nonce st ss.length, state := .Initiating }])
  /-- `owner` answers message one `{na, peer}`. -/
  | respond (owner peer : Std.U8) (c : Ct) (na : N) : owner ≠ ADVERSARY →
      pe.dec st owner c = some (.One na peer) →
      PStep pe lowe st ss
        (.Sent (pe.enc st peer (.Two na (pe.nonce st ss.length) owner)).1,
          (pe.enc st peer (.Two na (pe.nonce st ss.length) owner)).2,
          ss ++ [{ owner, peer, nonce := pe.nonce st ss.length, state := .Responding }])
  /-- The initiator session `k` accepts message two `{na, nb, responder}`. -/
  | initiated (k : Nat) (s : Session N) (c : Ct) (na nb : N) (responder : Std.U8) :
      ss[k]? = some s → s.state = .Initiating →
      pe.dec st s.owner c = some (.Two na nb responder) →
      (pe.same st na s.nonce).1 = true → (lowe = true → responder = s.peer) →
      PStep pe lowe st ss
        (.Sent (pe.enc (pe.same st na s.nonce).2 s.peer (.Three nb)).1,
          (pe.enc (pe.same st na s.nonce).2 s.peer (.Three nb)).2,
          ss.set k { s with state := .Done })
  /-- The responder session `k` accepts message three `{nb}`. -/
  | responded (k : Nat) (s : Session N) (c : Ct) (nb : N) :
      ss[k]? = some s → s.state = .Responding →
      pe.dec st s.owner c = some (.Three nb) →
      (pe.same st nb s.nonce).1 = true →
      PStep pe lowe st ss (.Accepted, (pe.same st nb s.nonce).2, ss.set k { s with state := .Done })

theorem pstep_spec (pe : PEnv S N Ct) (lowe : Bool) (st : S) (ss : List (Session N))
    (a : Action Ct) : PStep pe lowe st ss (pstep pe lowe st ss a) := by
  cases a with
  | Start owner peer =>
    simp only [pstep]
    split
    · exact .reject
    · exact .start owner peer ‹_›
  | Respond owner msg =>
    simp only [pstep]
    split
    · exact .reject
    · split
      · exact .respond owner _ msg _ ‹_› ‹_›
      · exact .reject
  | Deliver k msg =>
    simp only [pstep]
    split
    · exact .reject
    · rename_i s hs
      split
      · split
        · split
          · rename_i h
            exact .initiated k.val s msg _ _ _ hs ‹_› ‹_› h.1 h.2
          · exact .mismatch _ _
        · exact .reject
      · split
        · split
          · exact .responded k.val s msg _ hs ‹_› ‹_› ‹_›
          · exact .mismatch _ _
        · exact .reject
      · exact .reject

/-- A step keeps every session's owner, peer and nonce. It adds at most one
session, whose nonce is the environment's nonce for its index. -/
theorem PStep.sessions {pe : PEnv S N Ct} {lowe : Bool} {st st' : S} {ss ss' : List (Session N)}
    {r : Response Ct} (h : PStep pe lowe st ss (r, st', ss')) :
    ss.length ≤ ss'.length ∧ ss'.length ≤ ss.length + 1 ∧
      (∀ (k : Nat) (s : Session N), ss[k]? = some s →
        ∃ s', ss'[k]? = some s' ∧ s'.owner = s.owner ∧ s'.peer = s.peer ∧ s'.nonce = s.nonce) ∧
      (∀ s', ss'[ss.length]? = some s' → s'.nonce = pe.nonce st ss.length) := by
  have hset : ∀ (j : Nat) (s0 : Session N), ss[j]? = some s0 →
      ∀ (k : Nat) (s : Session N), ss[k]? = some s →
        ∃ s' : Session N, (ss.set j { s0 with state := .Done })[k]? = some s' ∧
        s'.owner = s.owner ∧ s'.peer = s.peer ∧ s'.nonce = s.nonce := by
    intro j s0 hj k s hk
    by_cases hjk : j = k
    · subst hjk
      rw [hj] at hk; cases hk
      exact ⟨{ s0 with state := .Done }, by simp [(List.getElem?_eq_some_iff.mp hj).1],
        rfl, rfl, rfl⟩
    · exact ⟨s, by simp [List.getElem?_set_ne hjk, hk], rfl, rfl, rfl⟩
  have happ : ∀ (x : Session N) (k : Nat) (s : Session N), ss[k]? = some s →
      ∃ s' : Session N, (ss ++ [x])[k]? = some s' ∧
      s'.owner = s.owner ∧ s'.peer = s.peer ∧ s'.nonce = s.nonce := by
    intro x k s hk
    exact ⟨s, by simp [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hk).1, hk],
      rfl, rfl, rfl⟩
  cases h with
  | reject | mismatch => exact ⟨by simp, by simp, fun k s hk => ⟨s, hk, rfl, rfl, rfl⟩, by simp⟩
  | start | respond => exact ⟨by simp, by simp, happ _, by simp⟩
  | initiated k s _ _ _ _ hk | responded k s _ _ hk => exact ⟨by simp, by simp, hset k s hk, by simp⟩

/-- A step changes the state by at most one `same` followed by at most one
`enc`. -/
theorem PStep.state {pe : PEnv S N Ct} {lowe : Bool} {st st' : S} {ss ss' : List (Session N)}
    {r : Response Ct} (h : PStep pe lowe st ss (r, st', ss')) :
    ∃ st1, (st1 = st ∨ ∃ x y, st1 = (pe.same st x y).2) ∧
      (st' = st1 ∨ ∃ dst m, st' = (pe.enc st1 dst m).2) := by
  cases h with
  | reject => exact ⟨st, .inl rfl, .inl rfl⟩
  | mismatch x y | responded _ _ _ _ _ _ _ _ => exact ⟨_, .inr ⟨_, _, rfl⟩, .inl rfl⟩
  | start | respond => exact ⟨st, .inl rfl, .inr ⟨_, _, rfl⟩⟩
  | initiated => exact ⟨_, .inr ⟨_, _, rfl⟩, .inr ⟨_, _, rfl⟩⟩

/-! ## Messages, sessions and tables -/

/-- Applies `f` to every nonce of a message. -/
def msgMap (f : N → M) : Msg N → Msg M
  | .One a x => .One (f a) x
  | .Two a b x => .Two (f a) (f b) x
  | .Three a => .Three (f a)

/-- Applies `f` to the nonce of a session. -/
def sessMap (f : N → M) (s : Session N) : Session M :=
  { owner := s.owner, peer := s.peer, nonce := f s.nonce, state := s.state }

/-- Applies `f` to every nonce of a table entry. -/
def entryMap (f : N → M) (e : Entry Ct N) : Entry Ct M :=
  { «to» := e.«to», ct := e.ct, msg := msgMap f e.msg }

/-- `nsl.lookup` on a list. -/
def lookupF : List (Entry Ct N) → Std.U8 → Ct → Option (Msg N)
  | [], _, _ => none
  | e :: es, who, c =>
    open Classical in if e.«to» = who ∧ e.ct = c then some e.msg else lookupF es who c

theorem lookupF_map (f : N → M) (l : List (Entry Ct N)) (who : Std.U8) (c : Ct) :
    lookupF (l.map (entryMap f)) who c = (lookupF l who c).map (msgMap f) := by
  induction l with
  | nil => rfl
  | cons e es ih => simp only [List.map_cons, lookupF, entryMap]; split <;> simp_all

theorem lookupF_mem {l : List (Entry Ct N)} {who : Std.U8} {c : Ct} {m : Msg N}
    (h : lookupF l who c = some m) : ∃ e ∈ l, e.«to» = who ∧ e.msg = m := by
  induction l with
  | nil => simp [lookupF] at h
  | cons e es ih =>
    simp only [lookupF] at h
    split at h
    · exact ⟨e, by simp, by simp_all, by simp_all⟩
    · obtain ⟨e', he', h'⟩ := ih h
      exact ⟨e', by simp [he'], h'⟩

/-- `nsl.concretize`. -/
def concF : Msg Sym → Option (Msg Std.U64)
  | .One (.Val a) x => some (.One a x)
  | .Two (.Val a) (.Val b) x => some (.Two a b x)
  | .Three (.Val a) => some (.Three a)
  | _ => none

/-! ## The three worlds -/

/-- The state of `World` over `RealOracle`. -/
structure RealSt where
  /-- The number of encryptions to the adversary. -/
  acount : Nat
  /-- The number of encryptions by the oracle. -/
  ocount : Nat

/-- `World` over `RealOracle`, with tape `t` and oracle tape `u`. -/
def realEnv (F : PkeF Seed Coins Pk Sk Ct) (t u : TapeF Seed Coins) : PEnv RealSt Std.U64 Ct where
  nonce _ k := t.nonce k
  same st a b := (decide (a = b), st)
  enc st dst m :=
    if dst = ADVERSARY then (F.encTo t st.acount dst m, { st with acount := st.acount + 1 })
    else (F.encTo u st.ocount dst m, { st with ocount := st.ocount + 1 })
  dec _ who c := F.decBy u who c

/-- The state of `World` over `IdealOracle`. -/
structure IdealSt (Ct : Type _) where
  acount : Nat
  ocount : Nat
  table : List (Entry Ct Std.U64)

/-- `World` over `IdealOracle`, with tape `t` and oracle tape `u`. -/
def idealEnv (F : PkeF Seed Coins Pk Sk Ct) (t u : TapeF Seed Coins) :
    PEnv (IdealSt Ct) Std.U64 Ct where
  nonce _ k := t.nonce k
  same st a b := (decide (a = b), st)
  enc st dst m :=
    if dst = ADVERSARY then (F.encTo t st.acount dst m, { st with acount := st.acount + 1 })
    else
      let ct := F.encTo u st.ocount dst BLANK
      (ct, { st with ocount := st.ocount + 1, table := st.table ++ [{ «to» := dst, ct, msg := m }] })
  dec st who c :=
    match lookupF st.table who c with
    | some m => some m
    | none => F.decBy u who c

/-- The state of `Symbolic`. -/
structure SymSt (Ct : Type _) where
  acount : Nat
  ocount : Nat
  table : List (Entry Ct Sym)
  guesses : List Std.U64
  leaked : Bool

/-- `Symbolic` with tape `t`, oracle tape `u` and secret session `j`. -/
def symEnv (F : PkeF Seed Coins Pk Sk Ct) (t u : TapeF Seed Coins) (j : Nat) :
    PEnv (SymSt Ct) Sym Ct where
  nonce _ k := if k = j then .Secret else .Val (t.nonce k)
  same st a b :=
    match a, b with
    | .Val x, .Val y => (decide (x = y), st)
    | .Secret, .Secret => (true, st)
    | .Val x, .Secret | .Secret, .Val x => (false, { st with guesses := st.guesses ++ [x] })
  enc st dst m :=
    if dst = ADVERSARY then
      match concF m with
      | some m => (F.encTo t st.acount dst m, { st with acount := st.acount + 1 })
      | none => (F.encTo t st.acount dst BLANK, { st with acount := st.acount + 1, leaked := true })
    else
      let ct := F.encTo u st.ocount dst BLANK
      (ct, { st with ocount := st.ocount + 1, table := st.table ++ [{ «to» := dst, ct, msg := m }] })
  dec st who c :=
    match lookupF st.table who c with
    | some m => some m
    | none => (F.decBy u who c).map (msgMap Sym.Val)

/-! ## Counters

Each step increments each counter at most once, so after `k` steps no counter
exceeds `k`. The extracted code needs this to rule out overflow. -/

/-- No counter of the real world exceeds `k`. -/
def RealSt.Fits (st : RealSt) (k : Nat) : Prop := st.acount ≤ k ∧ st.ocount ≤ k

/-- No counter or table of the ideal world exceeds `k`. -/
def IdealSt.Fits (st : IdealSt Ct) (k : Nat) : Prop :=
  st.acount ≤ k ∧ st.ocount ≤ k ∧ st.table.length ≤ k

/-- No counter, table or guess list of the symbolic world exceeds `k`. -/
def SymSt.Fits (st : SymSt Ct) (k : Nat) : Prop :=
  st.acount ≤ k ∧ st.ocount ≤ k ∧ st.table.length ≤ k ∧ st.guesses.length ≤ k

variable {F : PkeF Seed Coins Pk Sk Ct} {t u : TapeF Seed Coins} {lowe : Bool}

theorem realEnv_fits {st st' : RealSt} {ss ss' : List (Session Std.U64)} {r : Response Ct}
    {k : Nat} (h : PStep (realEnv F t u) lowe st ss (r, st', ss')) (hk : st.Fits k) :
    st'.Fits (k + 1) := by
  obtain ⟨st1, h1, h2⟩ := h.state
  have e1 : st1 = st := by rcases h1 with rfl | ⟨x, y, rfl⟩ <;> rfl
  subst e1
  rcases h2 with rfl | ⟨dst, m, rfl⟩
  · exact ⟨by have := hk.1; omega, by have := hk.2; omega⟩
  · simp only [realEnv]; split <;> simp_all [RealSt.Fits] <;> omega

theorem idealEnv_fits {st st' : IdealSt Ct} {ss ss' : List (Session Std.U64)} {r : Response Ct}
    {k : Nat} (h : PStep (idealEnv F t u) lowe st ss (r, st', ss')) (hk : st.Fits k) :
    st'.Fits (k + 1) := by
  obtain ⟨st1, h1, h2⟩ := h.state
  have e1 : st1 = st := by rcases h1 with rfl | ⟨x, y, rfl⟩ <;> rfl
  subst e1
  obtain ⟨hk1, hk2, hk3⟩ := hk
  rcases h2 with rfl | ⟨dst, m, rfl⟩
  · exact ⟨by omega, by omega, by omega⟩
  · simp only [idealEnv]; split <;> simp_all [IdealSt.Fits] <;> omega

/-- What one step does to the symbolic state: it records at most one guess
and never clears `leaked`. -/
theorem symEnv_step {j : Nat} {st st' : SymSt Ct} {ss ss' : List (Session Sym)} {r : Response Ct}
    (h : PStep (symEnv F t u j) lowe st ss (r, st', ss')) :
    st.guesses <+: st'.guesses ∧ st'.guesses.length ≤ st.guesses.length + 1 ∧
      (st.leaked = true → st'.leaked = true) ∧ ∀ k, st.Fits k → st'.Fits (k + 1) := by
  obtain ⟨st1, h1, h2⟩ := h.state
  have e1 : st1.acount = st.acount ∧ st1.ocount = st.ocount ∧ st1.table = st.table ∧
      st1.leaked = st.leaked ∧ st.guesses <+: st1.guesses ∧
      st1.guesses.length ≤ st.guesses.length + 1 := by
    rcases h1 with rfl | ⟨x, y, rfl⟩
    · simp
    · cases x <;> cases y <;> simp [symEnv]
  have e2 : st'.acount ≤ st1.acount + 1 ∧ st'.ocount ≤ st1.ocount + 1 ∧
      st'.table.length ≤ st1.table.length + 1 ∧ st'.guesses = st1.guesses ∧
      (st1.leaked = true → st'.leaked = true) := by
    rcases h2 with rfl | ⟨dst, m, rfl⟩
    · simp
    · simp only [symEnv]; split
      · split <;> simp
      · simp
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := e1
  obtain ⟨b1, b2, b3, b4, b5⟩ := e2
  refine ⟨b4 ▸ a5, b4 ▸ a6, fun hl => b5 (a4 ▸ hl), fun k hk => ?_⟩
  obtain ⟨c1, c2, c3, c4⟩ := hk
  rw [a3] at b3
  exact ⟨by omega, by omega, by omega, by rw [b4]; omega⟩


/-! ## The keys of the secrecy game -/

/-- The agent named `a`, for `a < 256`. -/
def agentOf (a : Nat) : Std.U8 := ⟨BitVec.ofNat 8 a⟩

/-- The public keys the secrecy game gives the adversary, indexed by agent:
the adversary's own from tape `t`, then those of the honest agents from the
oracle tape `u`. -/
def publicKeys (F : PkeF Seed Coins Pk Sk Ct) (t u : TapeF Seed Coins) : List Pk :=
  (F.keygen (t.seed ADVERSARY)).1 ::
    (List.range' 1 255).map fun a => (F.keygen (u.seed (agentOf a))).1

end examples.nsl.Model
