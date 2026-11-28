module

public import RustExamples.Gen.Specs
public import RustExamples.Merkle.Lawful
import RustExamples.Merkle.Completeness
import RustExamples.Merkle.Binding

/-! # What is proved about the Merkle tree

The audit statements are the hax contracts on `completeness` and `binding`
and their shared `lawful_hash` predicate in `examples/src/merkle.rs`. The
proofs below discharge the generated specifications using the original
Aeneas theorems. `lawful_hash_iff` checks the assumptions in both directions.
-/

public section

open Aeneas Aeneas.Std Result

namespace examples.merkle

/-- **Completeness.** For every list of leaves `data` and every `index` into
it, the tree built from `data` has a root, the proof it produces for `index`
verifies against that root with the true size, and none of this panics. An
out-of-range `index` makes `completeness` return `true` trivially. -/
theorem completeness_spec {Hs D : Type _} (H : Hash Hs D) (hH : H.Lawful)
    (data : Slice (alloc.vec.Vec Std.U8)) (index : Std.Usize) :
    completeness H data index = ok true :=
  Completeness.completeness_spec H hH data index

/-- **Binding.** Two proofs that verify against the same `root` and `index`,
for different data, yield a collision in `H` (a `Collision` that
`is_collision` accepts). This holds even if each proof is checked against a
different claimed tree size `n1`, `n2`, so the size need not be trusted. -/
theorem binding_spec {Hs D : Type _} (H : Hash Hs D) (hH : H.Lawful)
    (root : D) (index n1 : Std.Usize) (d1 : Slice Std.U8) (p1 : Slice D)
    (n2 : Std.Usize) (d2 : Slice Std.U8) (p2 : Slice D) :
    binding H root index n1 d1 p1 n2 d2 p2 = ok true :=
  Binding.binding_spec H hH root index n1 d1 p1 n2 d2 p2

/-- The generated postcondition requires successful evaluation and a true result. -/
private theorem returns_true {m : Result Bool} (h : m = ok true) :
    m ⦃ b => (ok b).holds ⦄ := by simp [h, HaxProp.truth]

/-- The contract on the Rust completeness property. -/
theorem completeness.spec.proof {Hs D : Type _} (H : Hash Hs D)
    (data : Slice (alloc.vec.Vec Std.U8)) (index : Std.Usize) :
    completeness.spec H data index := by
  intro law
  exact returns_true (completeness_spec H ((lawful_hash_iff H).mp law) data index)

/-- The contract on the Rust binding property. -/
theorem binding.spec.proof {Hs D : Type _} (H : Hash Hs D)
    (root : D) (index n1 : Std.Usize) (d1 : Slice Std.U8) (p1 : Slice D)
    (n2 : Std.Usize) (d2 : Slice Std.U8) (p2 : Slice D) :
    binding.spec H root index n1 d1 p1 n2 d2 p2 := by
  intro law
  exact returns_true (binding_spec H ((lawful_hash_iff H).mp law) root index n1 d1 p1 n2 d2 p2)

/-- info: 'examples.merkle.completeness.spec.proof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms completeness.spec.proof

/-- info: 'examples.merkle.binding.spec.proof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms binding.spec.proof

end examples.merkle
