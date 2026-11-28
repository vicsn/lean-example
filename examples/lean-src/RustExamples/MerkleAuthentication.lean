module

public import RustExamples.Gen.Specs
public import RustExamples.MerkleAuthenticationRoles
public import RustExamples.MerkleAuthenticationRecipes
import all DY.Actions.ProtocolEvent
import all DY.Actions.LongTermKeys
import all DY.Actions.PersistentLocalState
import all DY.Actions.PersistentGlobalState

/-! The Rust history checker instantiated on dylean's reachable Merkle traces. -/
open Aeneas Aeneas.Std Result
open DY DY.Example.MerkleTree

namespace examples.merkle_authentication

public abbrev ReachableTrace := { tr : ExecTrace // tr.Reachable reachability }
private structure TraceQuery where
  trace : ReachableTrace
  server : Participant
  element : Bytes

private abbrev Compromise := PersistentGlobalState.Compromise.CompromiseEvent
  (PersistentLocalState.LocalState (LongTermKeys.SecretKeyState "MerkleTree PKI"))

private def keyLeak (q : TraceQuery) (t : Nat) : Prop :=
  ∃ sk : Bytes, q.trace.val.EventLoggedAt (⟨⟨q.server, ⟨sk⟩⟩⟩ : Compromise) t

private noncomputable def observation (q : TraceQuery) (t : Nat) : Observation := by
  classical
  exact if keyLeak q t then .KeyCompromised
  else if q.trace.val.EventLoggedAt (.ServerAuthenticated q.server q.element : TheEvent) t then .Authenticated
  else if q.trace.val.EventLoggedAt (.ClientAccept q.server q.element : TheEvent) t then .Accepted
  else .Other

private theorem event_excludes_leak (q : TraceQuery) (t : Nat) (event : TheEvent)
    (logged : q.trace.val.EventLoggedAt event t) : ¬ keyLeak q t := by
  rintro ⟨sk, leaked⟩
  rw [Trace.EventLoggedAt, Trace.at?_eq_some] at logged leaked
  obtain ⟨ht, eq₁⟩ := logged
  obtain ⟨_, eq₂⟩ := leaked
  have eq := eq₁.symm.trans eq₂
  have different : (TraceEntryHas.inj (α := ExecTrace.Entry) (ProtocolEvent.ExecEntryT.mk event)) ≠
      TraceEntryHas.inj (ProtocolEvent.ExecEntryT.mk (⟨⟨q.server, ⟨sk⟩⟩⟩ : Compromise)) := by
    intro h
    injection h with tags
    contradiction
  exact different eq

private theorem accept_iff (q : TraceQuery) (t : Nat) :
    observation q t = .Accepted ↔ q.trace.val.EventLoggedAt (TheEvent.ClientAccept q.server q.element) t := by
  constructor
  · unfold observation
    repeat' split
    all_goals grind
  · intro h
    have hn := event_excludes_leak q t _ h
    have other : ¬ q.trace.val.EventLoggedAt (TheEvent.ServerAuthenticated q.server q.element) t := by
      rw [Trace.EventLoggedAt_eq_getEventAt] at h ⊢
      grind
    simp [observation, hn, other, h]

private def readObservation (q : TraceQuery) (t : Nat) : RustM Observation :=
  let event := match q.trace.val.getEventAt TheEvent t with
    | some (.ServerAuthenticated s e) => Event.ServerAuthenticated (s == q.server) (decide (e = q.element))
    | some (.ClientAccept s e) => Event.ClientAccept (s == q.server) (decide (e = q.element))
    | none => Event.Other
  let compromised := match q.trace.val.getEventAt Compromise t with
    | some e => e.state.participant == q.server
    | none => false
  classify event compromised

private theorem readObservation_eq (q : TraceQuery) (t : Nat) :
    readObservation q t = ok (observation q t) := by
  classical
  unfold readObservation observation keyLeak
  simp only [Trace.EventLoggedAt_eq_getEventAt]
  cases he : q.trace.val.getEventAt TheEvent t
  case' some e => cases e
  all_goals cases hc : q.trace.val.getEventAt Compromise t with
    | none => first | solve | simp [classify] | (simp [classify]; grind)
    | some e =>
      obtain ⟨⟨s,⟨sk⟩⟩⟩ := e
      simp [classify]; grind

private def runRole (tr : ReachableTrace) (config : ReachabilityConfig)
    [ReachabilityConfig.Has config reachability] (input : config.Input)
    (program : Traceful (config.step input).1) (same : program = (config.step input).2)
    (enabled : config.PreCond input tr.val) : ReachableTrace :=
  ⟨(program.run tr.val).snd.val, by
    rw [same, ReachabilityConfig.Has.pf_step config reachability]
    exact Trace.Reachable.Step _ ((ReachabilityConfig.Has.pf_pre input _).mp enabled) tr.property⟩

private def sendRecipe (tr : ReachableTrace) (r : roles.Recipe) : RustM ReachableTrace := do
  let out ← roles.derive (roles.deductions tr.val) () r
  match out with
  | none => ok tr
  | some b => ok (runRole tr Network.reachability b.val (Network.sendMessage b.val) rfl b.property)

private theorem sendRecipe_total (tr : ReachableTrace) (r : roles.Recipe) :
    ∃ tr', sendRecipe tr r = ok tr' := by
  obtain ⟨out, h⟩ := roles.derive_total tr.val r
  cases out <;> simp only [sendRecipe, h, bind_ok] <;> exact ⟨_, rfl⟩

/-- Interpret the extracted role programs and attacker recipes on dylean traces. -/
public def symbolic : Execution ReachableTrace Participant Bytes where
  empty := ok ⟨_, Trace.Reachable.Base⟩
  send := sendRecipe
  random tr n := ok (runRole tr Random.reachability n.val _ rfl trivial)
  generate_key tr s := ok (runRole tr (LongTermKeys.generateKeyPair.reachability "MerkleTree PKI") s _ rfl trivial)
  compromise_key tr k := ok (runRole tr (LongTermKeys.compromisePrivateKey.reachability "MerkleTree PKI") k.val _ rfl trivial)
  compromise_state tr h := ok (runRole tr ServerState.compromise.reachability h.val _ rfl trivial)
  authenticate tr s msgs k :=
    let hs := msgs.val.map UScalar.val
    ok (runRole tr Server.authenticate.reachability (s, hs, k.val)
      (roles.serverProgram s hs k.val) (roles.serverProgram_eq ..) trivial)
  prove_inclusion tr s h i :=
    ok (runRole tr Server.proveInclusion.reachability (s, i.val, h.val)
      (roles.proverProgram s i.val h.val) (roles.proverProgram_eq ..) trivial)
  check_inclusion tr s r p k :=
    ok (runRole tr Client.checkInclusion.reachability (s, r.val, p.val, k.val)
      (roles.clientProgram s r.val p.val k.val) (roles.clientProgram_eq ..) trivial)
  HistoryInst := ⟨fun tr s e t => readObservation ⟨tr,s,e⟩ t.val⟩

private abbrev traceHistory := symbolic.HistoryInst

private def priorWitness (q : TraceQuery) (t : Nat) : Prop :=
  ∃ j < t, observation q j = .Authenticated ∨ observation q j = .KeyCompromised

private theorem prior_succ (q : TraceQuery) (n : Nat) :
    priorWitness q (n + 1) ↔ priorWitness q n ∨
      observation q n = .Authenticated ∨ observation q n = .KeyCompromised := by
  unfold priorWitness
  constructor
  · rintro ⟨i, hi, hw⟩
    by_cases eq : i = n
    · subst i; exact Or.inr hw
    · exact Or.inl ⟨i, by omega, hw⟩
  · rintro (⟨i, hi, hw⟩ | hw)
    · exact ⟨i, by omega, hw⟩
    · exact ⟨n, by omega, hw⟩

private theorem scan (q : TraceQuery) (i : Usize) :
    check_history_loop traceHistory q.trace q.server q.element i
      ⦃ res => res = true ↔ priorWitness q i.val ⦄ := by
  generalize hn : i.val = n
  induction n using Nat.strong_induction_on generalizing i with
  | h n ih =>
    subst n
    unfold check_history_loop
    split
    · step as ⟨j, hj⟩
      have lookup : traceHistory.at q.trace q.server q.element j = ok (observation q j.val) :=
        readObservation_eq q j.val
      rw [lookup]
      have prev : i.val = j.val + 1 := by omega
      cases h : observation q j.val <;> simp [prev, prior_succ, h]
      all_goals exact ih j.val (by omega) j rfl
    · have hz : i.val = 0 := by scalar_tac
      simp [priorWitness, hz]

private theorem prefix_logged {E : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)]
    (tr : ExecTrace) (t : Nat) (e : E) :
    (tr.prefix t).EventLogged e ↔ ∃ j < t, tr.EventLoggedAt e j := by
  constructor
  · rintro ⟨j, he⟩
    have hj := Trace.EventLoggedAt_implies_i_le_length _ _ _ he
    rw [Trace.prefix_length] at hj
    exact ⟨j, by omega, Trace.EventLoggedAt_le _ _ _ _ (Trace.prefix_le_self ..) he⟩
  · rintro ⟨j, hj, he⟩
    have hj' := Trace.EventLoggedAt_implies_i_le_length _ _ _ he
    exact ⟨j, Trace.EventLoggedAt_le' _ _ _ _ (by rw [Trace.prefix_length]; omega)
      (Trace.prefix_le_self ..) he⟩

/-- Both directions ensure that the Rust prefix test accepts exactly the two
witnesses in the upstream statement, including compromise of any server key. -/
private theorem prefix_witness_iff (q : TraceQuery) (t : Nat) :
    (∃ j < t, observation q j = .Authenticated ∨ observation q j = .KeyCompromised) ↔
    (q.trace.val.prefix t).EventLogged (TheEvent.ServerAuthenticated q.server q.element) ∨
      ∃ pk, LongTermKeys.LongTermKeyCompromised "MerkleTree PKI" q.server pk (q.trace.val.prefix t) := by
  simp only [LongTermKeys.LongTermKeyCompromised, PersistentLocalState.LocalStateCompromised,
    PersistentGlobalState.GlobalStateCompromised, prefix_logged]
  constructor
  · rintro ⟨j, before, witness⟩
    by_cases leak : keyLeak q j
    · obtain ⟨sk, logged⟩ := leak
      exact Or.inr ⟨_, sk, rfl, j, before, logged⟩
    · left
      refine ⟨j, before, ?_⟩
      unfold observation at witness
      repeat' split at witness
      all_goals grind
  · rintro (⟨j, before, logged⟩ | ⟨_, sk, _, j, before, logged⟩)
    · exact ⟨j, before, by by_cases leak : keyLeak q j <;> simp [observation, leak, logged]⟩
    · have leak : keyLeak q j := ⟨sk, logged⟩
      exact ⟨j, before, Or.inr (by simp [observation, leak])⟩

private theorem history_ok (q : TraceQuery) (time : Usize) :
    check_history traceHistory q.trace q.server q.element time ⦃ res => res = true ⦄ := by
  unfold check_history
  have lookup : traceHistory.at q.trace q.server q.element time = ok (observation q time.val) := readObservation_eq q time.val
  rw [lookup]
  cases h : observation q time.val
  all_goals try simp
  have ha := (accept_iff q time.val).mp h
  have witness := (prefix_witness_iff q time.val).mpr
    (DY.Example.MerkleTree.client_authentication _ _ _ _ q.trace.property ha)
  have prior : priorWitness q time.val := witness
  simpa only [prior, iff_true] using scan q time

private theorem run_loop (actions : Slice (Action Participant)) (tr : ReachableTrace) (i : Usize) :
    execute_loop symbolic actions tr i ⦃ _ => True ⦄ := by
  unfold execute_loop
  dsimp only
  split
  · step as ⟨a, ha⟩
    cases a <;> simp [symbolic]
    case Send r =>
      obtain ⟨_, h⟩ := sendRecipe_total tr r
      rw [h]
      simp
      step as ⟨next, hn⟩
      apply run_loop
    all_goals
      step as ⟨next, hn⟩
      apply run_loop
  · simp
termination_by actions.length - i.val
decreasing_by all_goals scalar_decr_tac

/-- The generated Rust contract on arbitrary scripts under the symbolic execution semantics. -/
public theorem client_authentication.spec.proof (actions : Slice (Action Participant))
    (server : Participant) (element : Bytes) (time : Usize) :
    client_authentication.spec symbolic actions server element time := by
  unfold client_authentication.spec client_authentication client_authentication.post execute
  have h := run_loop actions ⟨_, Trace.Reachable.Base⟩ 0#usize
  have init : symbolic.empty = ok ⟨_, Trace.Reachable.Base⟩ := rfl
  rw [init]
  simp
  step with h
  exact history_ok ⟨_, server, element⟩ time

/-- info: 'examples.merkle_authentication.client_authentication.spec.proof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms client_authentication.spec.proof

end examples.merkle_authentication
