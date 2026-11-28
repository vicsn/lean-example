module

public import RustExamples.Merkle.Lawful
public import RustExamples.Merkle.Model

/-! # What the verifier computes

Each Rust function on the verifying side gets a `@[step]` spec saying that it
returns the value of a pure function, with no assumption on where its
arguments come from. In particular `inner_root_loop.spec` holds for every
proof, honest or not, so completeness and binding both build on it.

The hash functions of a lawful `H` never fail. `leafF`, `nodeF` and `sizeF`
are those functions with the `Result` removed, and the model in
`RustExamples.Merkle.Model` is used with `nodeF hH` as its node hash.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace examples.merkle
namespace Verify

open Model

variable {Hs D : Type _} {H : Hash Hs D} (hH : H.Lawful)

/-! ## Lawful hash functions as pure functions -/

/-- `H.leaf` as a pure function. -/
noncomputable def leafF (s : Slice Std.U8) : D := Classical.choose (hH.leaf_ok s)

/-- `H.node` as a pure function. -/
noncomputable def nodeF (a b : D) : D := Classical.choose (hH.node_ok a b)

/-- `H.size` as a pure function. -/
noncomputable def sizeF (a : D) (n : Std.Usize) : D := Classical.choose (hH.size_ok a n)

@[step] theorem leaf.spec (s : Slice Std.U8) : H.leaf s ⦃ d => d = leafF hH s ⦄ := by
  rw [Classical.choose_spec (hH.leaf_ok s)]; simp [leafF]

@[step] theorem node.spec (a b : D) : H.node a b ⦃ d => d = nodeF hH a b ⦄ := by
  rw [Classical.choose_spec (hH.node_ok a b)]; simp [nodeF]

@[step] theorem size.spec (a : D) (n : Std.Usize) : H.size a n ⦃ d => d = sizeF hH a n ⦄ := by
  rw [Classical.choose_spec (hH.size_ok a n)]; simp [sizeF]

include hH in
@[step] theorem eq.spec (a b : D) :
    H.corecmpEqInst.partialEqInst.eq a b ⦃ r => (r = true ↔ a = b) ⦄ := by
  simp [hH.eq_ok]

include hH in
@[step] theorem ne.spec (a b : D) :
    H.corecmpEqInst.partialEqInst.ne a b ⦃ r => (r = true ↔ a ≠ b) ⦄ := by
  simp [hH.ne_ok]

/-! ## Specs of the extracted functions -/

/-- **Spec theorem for `examples::merkle::has_sibling`** -/
@[step] theorem has_sibling.spec (index width : Std.Usize) (h : index.val < width.val) :
    has_sibling index width ⦃ b =>
      (b = true ↔ (index.val % 2 = 1 ∨ index.val + 1 < width.val)) ⦄ := by
  unfold has_sibling
  step*

/-- **Spec theorem for `examples::merkle::step`** -/
@[step] theorem step.spec (index : Std.Usize) (acc s : D) :
    merkle.step H index acc s ⦃ r => r = stepF (nodeF hH) index.val acc s ⦄ := by
  unfold merkle.step
  step* <;> grind [stepF]

/-- **Spec theorem for `examples::merkle::parent_width`** -/
@[step] theorem parent_width.spec (width : Std.Usize) :
    parent_width width ⦃ r => r.val = (width.val + 1) / 2 ⦄ := by
  unfold parent_width
  step*

/-- **Spec theorem for `examples::merkle::inner_root` (loop)**: from the node
`acc` at `index` on a level of `width` nodes, computes `innerRootF` of the
proof elements from `i` on. The proof is arbitrary. -/
@[step] theorem inner_root_loop.spec (proof : Slice D) (acc : D) (index width i : Std.Usize)
    (hi : index.val < width.val) (hip : i.val ≤ proof.length) :
    inner_root_loop H proof acc index width i ⦃ r =>
      r = innerRootF (nodeF hH) width.val index.val acc (proof.val.drop i.val) ⦄ := by
  unfold inner_root_loop
  step*
  all_goals rw [innerRootF_drop _ _ _ _ _ _ (by scalar_tac)]
  all_goals agrind
termination_by width.val
decreasing_by all_goals scalar_decr_tac

/-- What `inner_root` computes: `innerRootF` from the hash of `data`, or
`none` if `index` is out of range. -/
noncomputable def innerF (size index : Std.Usize) (data : Slice Std.U8) (proof : List D) :
    Option D :=
  if index.val < size.val then
    innerRootF (nodeF hH) size.val index.val (leafF hH data) proof
  else none

/-- **Spec theorem for `examples::merkle::inner_root`** -/
@[step] theorem inner_root.spec (size index : Std.Usize) (data : Slice Std.U8)
    (proof : Slice D) :
    inner_root H size index data proof ⦃ r => r = innerF hH size index data proof.val ⦄ := by
  unfold inner_root
  step* <;> simp_all [innerF]

/-- **Spec theorem for `examples::merkle::verify`**: accepts exactly when
`inner_root` returns a node whose size commitment is `root`. -/
@[step] theorem verify.spec (root : D) (size index : Std.Usize) (data : Slice Std.U8)
    (proof : Slice D) :
    verify H root size index data proof ⦃ b =>
      (b = true ↔
        ∃ r, innerF hH size index data proof.val = some r ∧ sizeF hH r size = root) ⦄ := by
  unfold verify
  step*

/-- A program that satisfies the spec `b = true` equals `ok true`, the form
in which `RustExamples.Merkle` states the theorems. -/
theorem eq_ok_of_spec {m : Result Bool} (h : m ⦃ b => b = true ⦄) : m = ok true := by
  cases m <;> simp_all

end Verify
end examples.merkle
