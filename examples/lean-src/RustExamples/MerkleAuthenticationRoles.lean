module

public import RustExamples.Gen.Funs
public import Examples.MerkleTree.SecurityTheorems
import all Examples.MerkleTree.Specification
import all DY.Trace.Monad

/-! Interpret the three Rust role programs using symbolic network, PKI and
Merkle primitives. The equalities include every intermediate trace entry and
the failure behavior, as well as the returned handles. -/
open DY DY.Example.MerkleTree
open Aeneas.Std

namespace examples.merkle_authentication.roles

private def script {n : Usize} (code : RustM (Aeneas.Std.Array op n))
    (interpret : List op → Traceful α) : Traceful α :=
  match code.«match» with
  | .ok ops => interpret ops.val
  | _ => failure

private def blank : Bytes := Literal.literalToBytes ByteArray.empty

private structure ClientState where
  vk : Bytes := blank
  signedRoot : SignedRootHash := ⟨⟨blank, 0⟩, blank⟩
  opening : ElementAndInclusionProof := ⟨blank, 0, []⟩

private def interpretClient (s : Participant) (r p k : Nat) :
    List Client → ClientState → Traceful Unit
  | [], _ => pure ()
  | op :: rest, st => do
    match op with
    | .LookupVerificationKey =>
      let vk ← LongTermKeys.getPublicKey "MerkleTree PKI" s k
      interpretClient s r p k rest { st with vk }
    | .ReceiveSignedRoot =>
      let wire ← Network.receiveMessage r
      let signedRoot ← DY.Comparse.parse wire
      interpretClient s r p k rest { st with signedRoot }
    | .ReceiveOpening =>
      let wire ← Network.receiveMessage p
      let opening ← DY.Comparse.parse wire
      interpretClient s r p k rest { st with opening }
    | .VerifyRootSignature =>
      guard (Signature.verify st.vk (DY.Comparse.serialize st.signedRoot.tbs) st.signedRoot.sig)
      interpretClient s r p k rest st
    | .CheckRootFromPath =>
      guard (inclusionProofToRootHash (.bytes) st.opening.inclusionProof st.opening.element st.opening.i
        st.signedRoot.tbs.length = st.signedRoot.tbs.rootHash)
      interpretClient s r p k rest st
    | .CheckIndexBounds =>
      guard (st.opening.i < st.signedRoot.tbs.length)
      interpretClient s r p k rest st
    | .LogClientAccept =>
      let _ ← ProtocolEvent.logEvent (TheEvent.ClientAccept s st.opening.element)
      interpretClient s r p k rest st

public def clientProgram (s : Participant) (r p k : Nat) : Traceful Unit :=
  script client (fun ops => interpretClient s r p k ops {})

private theorem guards (p q : Prop) [Decidable p] [Decidable q] [Decidable (p ∧ q)] (next : Traceful Unit) :
    (do guard p; guard q; next) = (do guard (p ∧ q); next) := by
  by_cases hp : p <;> by_cases hq : q <;> (simp [guard, hp, hq]; try rfl)

public theorem clientProgram_eq (s : Participant) (r p k : Nat) :
    clientProgram s r p k = DY.Example.MerkleTree.Client.checkInclusion s r p k := by
  simp [clientProgram, script, client, interpretClient, Aeneas.Std.Array.make_val, DY.Example.MerkleTree.Client.checkInclusion, checkInclusionProof, guards]
  repeat (apply congrArg _; funext _)
  exact (guards _ _ _).symm

private structure ServerRegisters where
  elements : _root_.Array Bytes := #[]
  sk : Bytes := blank
  nonce : Bytes := blank
  tbs : SignedRootHashTBS := ⟨blank, 0⟩
  sig : Bytes := blank
  msgHandle : Nat := 0
  stateHandle : Nat := 0

private def interpretServer (s : Participant) (handles : List Nat) (key : Nat) :
    List Server → ServerRegisters → Traceful (Nat × Nat)
  | [], st => pure (st.msgHandle, st.stateHandle)
  | op :: rest, st => do
    match op with
    | .ReceiveAndAuthenticateEachElement =>
      let mut elements := #[]
      for handle in handles do
        let msg ← Network.receiveMessage handle
        ProtocolEvent.logEvent (TheEvent.ServerAuthenticated s msg)
        elements := elements.push msg
      interpretServer s handles key rest { st with elements }
    | .LookupSigningKey =>
      let sk ← LongTermKeys.getPrivateKey "MerkleTree PKI" s key
      interpretServer s handles key rest { st with sk }
    | .ComputeRootAndLength =>
      let tbs := ⟨merkleTreeHash (.bytes) st.elements.toList, st.elements.size⟩
      interpretServer s handles key rest { st with tbs }
    | .GenerateSigningNonce =>
      let nonce ← Random.genRand 32
      interpretServer s handles key rest { st with nonce }
    | .SignRootAndLength =>
      let sig := Signature.sign st.sk st.nonce (DY.Comparse.serialize st.tbs)
      interpretServer s handles key rest { st with sig }
    | .PublishSignedRoot =>
      let msgHandle ← Network.sendMessage (DY.Comparse.serialize (⟨st.tbs, st.sig⟩ : SignedRootHash))
      interpretServer s handles key rest { st with msgHandle }
    | .StoreElements =>
      let stateHandle ← PersistentLocalState.storeLocalState s (⟨st.elements.toList⟩ : ServerState)
      interpretServer s handles key rest { st with stateHandle }

public def serverProgram (s : Participant) (handles : List Nat) (key : Nat) : Traceful (Nat × Nat) :=
  script server (fun ops => interpretServer s handles key ops {})

public theorem serverProgram_eq (s : Participant) (handles : List Nat) (key : Nat) :
    serverProgram s handles key = DY.Example.MerkleTree.Server.authenticate s handles key := by
  simp [serverProgram, script, server, interpretServer, Aeneas.Std.Array.make_val, DY.Example.MerkleTree.Server.authenticate]

private def interpretProver (s : Participant) (i h : Nat) :
    List Prover → List Bytes → Nat → Traceful Nat
  | [], _, sent => pure sent
  | op :: rest, elements, sent => do
    match op with
    | .LoadServerElements =>
      let state : ServerState ← PersistentLocalState.getLocalState s h
      interpretProver s i h rest state.elements sent
    | .SendOpeningForIndex =>
      if out : ¬ i < elements.length then failure else
      let msg : ElementAndInclusionProof :=
        ⟨elements[i], i, mkInclusionProof (.bytes) elements i (by omega)⟩
      let handle ← Network.sendMessage (DY.Comparse.serialize msg)
      interpretProver s i h rest elements handle

public def proverProgram (s : Participant) (i h : Nat) : Traceful Nat :=
  script prover (fun ops => interpretProver s i h ops [] 0)

public theorem proverProgram_eq (s : Participant) (i h : Nat) :
    proverProgram s i h = DY.Example.MerkleTree.Server.proveInclusion s i h := by
  simp [proverProgram, script, prover, interpretProver, Aeneas.Std.Array.make_val, DY.Example.MerkleTree.Server.proveInclusion]

  congr 1
  funext state
  split <;> split <;> first | rfl | omega

end examples.merkle_authentication.roles
