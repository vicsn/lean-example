module

public import RustExamples.Gen.Funs
public import Examples.MerkleTree.Instance

open DY DY.Example.MerkleTree
open Aeneas Aeneas.Std Result
namespace examples.merkle_authentication.roles

public abbrev Known (tr : ExecTrace) := { b : Bytes // b.AttackerKnows tr }

private def received (tr : ExecTrace) (i : Nat) : Option (Known tr) :=
  match h : tr.getMessageSentAt i with
  | none => none
  | some b => some ⟨b, DY.Trace.MessageSentAt_implies_AttackerKnows tr b i
      ((DY.Trace.MessageSentAt_eq_getMessageSentAt b i tr).mpr h)⟩

private def splitKnown (tr : ExecTrace) (b : Known tr) (left : Bool) : Option (Known tr) := do
  let pair ← b.val.view? Concat.Concat.SubF
  let n := pair.lhs.length
  match h : Concat.split b.val n with
  | none => none
  | some (l,r) =>
    have known : l.AttackerKnows tr ∧ r.AttackerKnows tr := by
      simpa [h] using Concat.attacker_knows_split b.val n tr b.property
    if left then some ⟨l,known.1⟩ else some ⟨r,known.2⟩

public def deductions (tr : ExecTrace) : Deductions Unit (Known tr) where
  receive _ h := ok (received tr h.val)
  literal _ v :=
    let b := ByteArray.mk ((v.val.map (fun x => x.val.toUInt8)).toArray)
    ok ⟨Literal.literalToBytes b, Literal.attacker_knows_literalToBytes b tr⟩
  concat _ l r := ok ⟨Concat.concat l.val r.val, Concat.attacker_knows_concat _ _ _ l.property r.property⟩
  split _ b left := ok (splitKnown tr b left)
  hash _ x := ok ⟨Hash.hash x.val, Hash.attacker_knows_hash _ _ x.property⟩
  vk _ x := ok ⟨Signature.vk x.val, Signature.attacker_knows_vk _ _ x.property⟩
  sign _ k n m := ok ⟨Signature.sign k.val n.val m.val,
    Signature.attacker_knows_sign _ _ _ _ k.property n.property m.property⟩

public theorem derive_total (tr : ExecTrace) (r : Recipe) :
    ∃ out, «derive» (deductions tr) () r = ok out := by
  induction r <;> (conv => enter [1, out, 1]; unfold «derive»)
  all_goals try casesm* ∃ _, _
  all_goals try casesm* Option _
  all_goals simp_all [deductions]

end examples.merkle_authentication.roles
