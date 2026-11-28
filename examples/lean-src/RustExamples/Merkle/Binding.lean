module

public import RustExamples.Merkle.Lawful
import RustExamples.Merkle.Verify

/-! Binding: two proofs that verify for different data yield a collision.

`Collides` says, in terms of the pure hash functions, which collisions
`is_collision` accepts. If both proofs verify, `RustExamples.Merkle.Verify` gives
two inner roots with the same size commitment, and `extract` finds a
collision from them:

* If the claimed sizes differ, the two size commitments collide.
* If the leaf hashes are equal, the leaves collide.
* Otherwise the loop walks both proofs in lockstep. Its invariant
  (`extract_loop1.spec`) is that the two accumulators differ while
  `innerRootF` of the remaining proofs gives roots with the same size
  commitment. Either two different pairs hash to the same node on the way up,
  or the paths end in different roots with the same size commitment.
-/

open Aeneas Aeneas.Std Result

namespace examples.merkle
namespace Binding

open Model Verify

section Impl

variable {Hs D : Type _} {H : Hash Hs D} (hH : H.Lawful)

/-- **Spec theorem for `examples::merkle::bytes_eq` (loop)**: compares the
bytes from `i` on. -/
@[step] theorem bytes_eq_loop.spec (a b : Slice Std.U8) (i : Std.Usize)
    (hlen : a.length = b.length) :
    bytes_eq_loop a b i ⦃ r => (r = true ↔ a.val.drop i.val = b.val.drop i.val) ⦄ := by
  unfold bytes_eq_loop
  step*
  · rw [List.drop_eq_getElem_cons (by scalar_tac : i.val < a.val.length),
      List.drop_eq_getElem_cons (by scalar_tac : i.val < b.val.length)]
    agrind
  · rw [List.drop_eq_getElem_cons (by scalar_tac : i.val < a.val.length),
      List.drop_eq_getElem_cons (by scalar_tac : i.val < b.val.length)]
    agrind
  · rw [List.drop_eq_nil_of_le (by scalar_tac : a.val.length ≤ i.val),
      List.drop_eq_nil_of_le (by scalar_tac : b.val.length ≤ i.val)]
    agrind
termination_by a.length - i.val
decreasing_by scalar_decr_tac

/-- **Spec theorem for `examples::merkle::bytes_eq`**: decides equality. -/
@[step] theorem bytes_eq.spec (a b : Slice Std.U8) :
    bytes_eq a b ⦃ r => (r = true ↔ a = b) ⦄ := by
  unfold bytes_eq
  step*
  simp_all [Slice.eq_iff]

/-- `c` is a collision in `H`: two different inputs to `leaf`, `node` or `size`
with the same digest. -/
def Collides : Collision D → Prop
  | .Leaf a b => a ≠ b ∧ leafF hH a = leafF hH b
  | .Node a b c d => (a ≠ c ∨ b ≠ d) ∧ nodeF hH a b = nodeF hH c d
  | .Size a n b m => (a ≠ b ∨ n ≠ m) ∧ sizeF hH a n = sizeF hH b m

/-- **Spec theorem for `examples::merkle::is_collision`** -/
@[step] theorem is_collision.spec (c : Collision D) :
    is_collision H c ⦃ b => (b = true ↔ Collides hH c) ⦄ := by
  unfold is_collision
  step* <;> agrind [Collides]

/-- **Spec theorem for `examples::merkle::extract` (loop)**: the lockstep
invariant. The accumulators `a` and `b` differ, yet both paths end in roots
with the same size commitment, so the loop finds a collision. -/
@[step] theorem extract_loop1.spec (n1 n2 : Std.Usize) (p1 p2 : Slice D) (a b : D)
    (index width i : Std.Usize) (hi : index.val < width.val)
    (hi1 : i.val ≤ p1.length) (hi2 : i.val ≤ p2.length) (hab : a ≠ b)
    (h : ∃ r1 r2, innerRootF (nodeF hH) width.val index.val a (p1.val.drop i.val) = some r1 ∧
      innerRootF (nodeF hH) width.val index.val b (p2.val.drop i.val) = some r2 ∧
      sizeF hH r1 n1 = sizeF hH r2 n2) :
    extract_loop1 H n1 p1 n2 p2 a b index width i ⦃ o =>
      ∃ c, o = some c ∧ Collides hH c ⦄ := by
  rw [innerRootF_drop _ _ _ _ p1.val _ hi1, innerRootF_drop _ _ _ _ p2.val _ hi2] at h
  unfold extract_loop1
  step* <;> agrind [Collides, stepF]
termination_by width.val
decreasing_by all_goals scalar_decr_tac

/-- **Spec theorem for `examples::merkle::extract`**: from two inner roots with
the same size commitment, for different data, returns a collision. -/
@[step] theorem extract.spec (index n1 : Std.Usize) (d1 : Slice Std.U8) (p1 : Slice D)
    (n2 : Std.Usize) (d2 : Slice Std.U8) (p2 : Slice D) (hd : d1 ≠ d2)
    (h : ∃ r1 r2, innerF hH n1 index d1 p1.val = some r1 ∧
      innerF hH n2 index d2 p2.val = some r2 ∧ sizeF hH r1 n1 = sizeF hH r2 n2) :
    extract H index n1 d1 p1 n2 d2 p2 ⦃ o => ∃ c, o = some c ∧ Collides hH c ⦄ := by
  obtain ⟨r1, r2, h1, h2, hr⟩ := h
  unfold extract
  step* <;> simp_all [Collides, innerF]

include hH in
/-- **Spec theorem for `examples::merkle::binding`** -/
theorem binding.spec (root : D) (index n1 : Std.Usize) (d1 : Slice Std.U8) (p1 : Slice D)
    (n2 : Std.Usize) (d2 : Slice Std.U8) (p2 : Slice D) :
    binding H root index n1 d1 p1 n2 d2 p2 ⦃ b => b = true ⦄ := by
  unfold binding
  step*

end Impl

/-- Binding: for every lawful `H`, two proofs that verify against the same
root and index for different data yield a collision in `H`. -/
public theorem binding_spec {Hs D : Type _} (H : Hash Hs D) (hH : H.Lawful)
    (root : D) (index n1 : Std.Usize) (d1 : Slice Std.U8) (p1 : Slice D)
    (n2 : Std.Usize) (d2 : Slice Std.U8) (p2 : Slice D) :
    binding H root index n1 d1 p1 n2 d2 p2 = ok true :=
  eq_ok_of_spec (binding.spec hH root index n1 d1 p1 n2 d2 p2)

end Binding

end examples.merkle
