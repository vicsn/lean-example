module

public import RustExamples.Merkle.Lawful
import RustExamples.Merkle.Verify

/-! Completeness: the honest proof for every leaf verifies.

Each function of `Tree` gets a `@[step]` spec relating it to the model in
`RustExamples.Merkle.Model`: `Tree::new` builds `levelsFrom` of the leaf hashes,
`Tree::root` returns the size commitment of the first node of `topOf`, and
`Tree::proof` returns `proofFrom`. `RustExamples.Merkle.Verify` shows that
`verify` computes `innerRootF`, and `Model.innerRootF_proofFrom` shows that
`innerRootF` of the honest proof is the first node of `topOf`.
-/

open Aeneas Aeneas.Std Result

namespace examples.merkle
namespace Completeness

open Model Verify

section Impl

variable {Hs D : Type _} {H : Hash Hs D} (hH : H.Lawful)

/-! ## Building the tree -/

/-- `Usize.max` is odd, so an even index below it is at most `Usize.max - 1`. -/
theorem usize_max_odd : Usize.max % 2 = 1 := by
  rcases Usize.bounds_eq with h | h <;> rw [h] <;> scalar_tac

/-- **Spec theorem for `examples::merkle::Tree::new` (loop 0)**: hashes the
remaining data into leaves. -/
@[step] theorem Tree.new_loop0.spec (data : Slice (alloc.vec.Vec Std.U8))
    (level : alloc.vec.Vec D) (i : Std.Usize)
    (hi : i.val ≤ data.length) (hlevel : level.length = i.val) :
    Tree.new_loop0 H data level i ⦃ res =>
      res.val = level.val ++ (data.val.drop i.val).map (fun v => leafF hH v.deref) ⦄ := by
  unfold Tree.new_loop0
  step*
  · agrind
  · rw [res_post, level1_post, i2_post, t_post, v_post,
      List.drop_eq_getElem_cons (by scalar_tac : i.val < data.val.length)]
    simp only [List.map_cons, List.append_assoc, List.singleton_append]
  · rw [List.drop_eq_nil_of_le (by scalar_tac : data.val.length ≤ i.val)]
    simp
termination_by data.length - i.val
decreasing_by scalar_decr_tac

/-- **Spec theorem for `examples::merkle::Tree::new` (loop 2)**: hashes the
remaining adjacent pairs of `level` into `next`. An odd last node is left for
the caller, at the returned index. -/
@[step] theorem Tree.new_loop1_loop0.spec (level next : alloc.vec.Vec D) (i : Std.Usize)
    (hi : i.val ≤ level.length) (heven : i.val % 2 = 0) (hnext : next.length ≤ i.val) :
    Tree.new_loop1_loop0 H level next i ⦃ next' j =>
      next'.val ++ level.val.drop j.val =
        next.val ++ nextLevel (nodeF hH) (level.val.drop i.val) ∧
      j.val ≤ level.length ∧ level.length ≤ j.val + 1 ⦄ := by
  have := usize_max_odd
  unfold Tree.new_loop1_loop0
  step*
  · agrind
  · rw [List.drop_eq_getElem_cons (by scalar_tac : i.val < level.val.length),
      List.drop_eq_getElem_cons (by scalar_tac : i.val + 1 < level.val.length)]
    agrind [nextLevel]
  · rw [nextLevel_of_length_le _ _ (by simp; scalar_tac)]
    agrind
termination_by level.length - i.val
decreasing_by scalar_decr_tac

/-- **Spec theorem for `examples::merkle::Tree::new` (loop 1)**: pushes
`level` and every level above it except the top onto `levels`, and returns
the top level. -/
@[step] theorem Tree.new_loop1.spec (level : alloc.vec.Vec D)
    (levels : alloc.vec.Vec (alloc.vec.Vec D))
    (hpos : 0 < level.length) (hsum : levels.length + level.length ≤ Usize.max) :
    Tree.new_loop1 H level levels ⦃ top lvls =>
      lvls.val.map alloc.vec.Vec.val ++ [top.val] =
        levels.val.map alloc.vec.Vec.val ++ levelsFrom (nodeF hH) level.val ∧
      lvls.length < Usize.max ⦄ := by
  have hnl := nextLevel_length (nodeF hH) level.val
  unfold Tree.new_loop1
  rw [levelsFrom.eq_def]
  step*
  · simp only [List.drop_zero, alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.nil_append]
      at next_post
    -- The odd last node moves up: either way, `next1` is the next level.
    have key : ∀ next1 : alloc.vec.Vec D, next1.val = next.val ++ level.val.drop i1.val →
        next1.val = nextLevel (nodeF hH) level.val ∧ next1.length < level.length ∧
          0 < next1.length := by
      intro next1 h
      rw [next_post] at h
      simp only [alloc.vec.Vec.length, h, hnl]; scalar_tac
    split
    · step as ⟨x, hx⟩
      step as ⟨next1, hnext1⟩
      have := key next1 (by
        rw [hnext1, List.drop_eq_getElem_cons (by scalar_tac),
          List.drop_eq_nil_of_le (by scalar_tac), hx])
      step*
      · agrind
      · simp_all
    · have := key next (by
        simp [List.drop_eq_nil_of_le (by scalar_tac : level.val.length ≤ i1.val)])
      step*
      · agrind
      · simp_all
termination_by level.length
decreasing_by all_goals agrind

/-- The tree's levels are those of the model above the leaves `l`. -/
def Tree.Models (self : Tree Hs D) (l : List D) : Prop :=
  self.levels.val.map alloc.vec.Vec.val = levelsFrom (nodeF hH) l

/-- **Spec theorem for `examples::merkle::Tree::new`**: the levels are the leaf
hashes and every level above them. -/
@[step] theorem Tree.new.spec (data : Slice (alloc.vec.Vec Std.U8)) (hpos : 0 < data.length) :
    Tree.new H data ⦃ tree =>
      Tree.Models hH tree (data.val.map (fun v => leafF hH v.deref)) ⦄ := by
  unfold Tree.new
  step*
  simp_all [Tree.Models]

variable {hH} in
theorem Tree.Models.getElem? {self : Tree Hs D} {l : List D} (h : Tree.Models hH self l)
    (k : Nat) (hk : k < self.levels.val.length) :
    (levelsFrom (nodeF hH) l)[k]? = some self.levels.val[k].val := by
  unfold Tree.Models at h; simp [← h, hk]

variable {hH} in
theorem Tree.Models.length {self : Tree Hs D} {l : List D} (h : Tree.Models hH self l) :
    self.levels.val.length = (levelsFrom (nodeF hH) l).length := by
  unfold Tree.Models at h; simp [← h]

/-! ## Reading the tree -/

/-- **Spec theorem for `examples::merkle::Tree::size`**: the number of leaves. -/
@[step] theorem Tree.size.spec (self : Tree Hs D) (l : List D) (hL : Tree.Models hH self l) :
    Tree.size H self ⦃ n => n.val = l.length ⦄ := by
  have := levelsFrom_getElem?_zero (nodeF hH) l
  have := levelsFrom_length_pos (nodeF hH) l
  have := hL.length
  unfold Tree.size
  step*
  have := hL.getElem? 0 (by scalar_tac)
  simp_all

/-- **Spec theorem for `examples::merkle::Tree::root`**: the size commitment of
the first node of the top level. -/
@[step] theorem Tree.root.spec (self : Tree Hs D) (l : List D)
    (hL : Tree.Models hH self l) (hpos : 0 < l.length) :
    Tree.root H self ⦃ r =>
      ∃ t m, (topOf (nodeF hH) l).head? = some t ∧ m.val = l.length ∧
        r = some (sizeF hH t m) ⦄ := by
  have := levelsFrom_getElem?_last (nodeF hH) l
  have := levelsFrom_length_pos (nodeF hH) l
  have := topOf_length (nodeF hH) l
  have := hL.length
  unfold Tree.root
  step*
  all_goals
    have := hL.getElem? i1.val (by scalar_tac)
    simp_all [List.head?_eq_getElem?]
    try agrind

/-- From level `k` up, the tree's levels are those of the model above `l`. This
is the invariant of the loop in `Tree::proof`, which climbs one level per
iteration. -/
def Tree.ModelsFrom (self : Tree Hs D) (k : Nat) (l : List D) : Prop :=
  (self.levels.val.map alloc.vec.Vec.val).drop k = levelsFrom (nodeF hH) l

section
variable {hH} {self : Tree Hs D} {k : Nat} {l : List D} (h : Tree.ModelsFrom hH self k l)
include h

/-- Level `k` of the tree is `l`. -/
theorem Tree.ModelsFrom.getElem :
    ∃ hk : k < self.levels.val.length, self.levels.val[k].val = l := by
  have := congrArg (·[0]?) h
  have := levelsFrom_getElem?_zero (nodeF hH) l
  grind

/-- If `l` is not the top level, the invariant holds one level up. -/
theorem Tree.ModelsFrom.succ (hl : 1 < l.length) :
    Tree.ModelsFrom hH self (k + 1) (nextLevel (nodeF hH) l) ∧
      k + 1 < self.levels.val.length := by
  have := levelsFrom_length_pos (nodeF hH) (nextLevel (nodeF hH) l)
  unfold Tree.ModelsFrom at *
  rw [levelsFrom.eq_def] at h
  simp only [hl, ↓reduceIte] at h
  have := congrArg List.length h
  refine ⟨by rw [← List.tail_drop, h, List.tail_cons], ?_⟩
  grind

/-- If `l` is the top level, `k` is the last level of the tree. -/
theorem Tree.ModelsFrom.last (hl : ¬ 1 < l.length) : k + 1 = self.levels.val.length := by
  have := congrArg List.length h
  rw [levelsFrom.eq_def] at this
  simp only [hl, ↓reduceIte] at this
  grind

end

/-- **Spec theorem for `examples::merkle::Tree::proof` (loop)**: appends the
siblings on the path of the node at `index` on level `k`. -/
@[step] theorem Tree.proof_loop.spec (self : Tree Hs D) (proof : alloc.vec.Vec D)
    (index k : Std.Usize) (l : List D) (hL : Tree.ModelsFrom hH self k.val l)
    (hidx : index.val < l.length) (hp : proof.length ≤ k.val) :
    Tree.proof_loop self proof index k ⦃ res =>
      res.val = proof.val ++ proofFrom (nodeF hH) l index.val ⦄ := by
  obtain ⟨hk, hlev⟩ := hL.getElem
  rw [proofFrom.eq_def]
  unfold Tree.proof_loop
  by_cases hl : 1 < l.length
  · obtain ⟨hL', hk'⟩ := hL.succ hl
    have hidx' : index.val / 2 < (nextLevel (nodeF hH) l).length := by
      rw [nextLevel_length]; agrind
    step as ⟨i, hi⟩
    rw [← hi] at hL'
    step*
    split
    · step* <;> simp_all [sib]; grind
    · step*
      split <;> step* <;> simp_all [sib]; grind
  · have := hL.last hl
    step*
termination_by self.levels.length - k.val
decreasing_by all_goals scalar_decr_tac

/-- **Spec theorem for `examples::merkle::Tree::proof`**: the siblings on the
path of leaf `index`. -/
@[step] theorem Tree.proof.spec (self : Tree Hs D) (l : List D) (hL : Tree.Models hH self l)
    (index : Std.Usize) (hidx : index.val < l.length) :
    Tree.proof H self index ⦃ r =>
      ∃ p, r = some p ∧ p.val = proofFrom (nodeF hH) l index.val ⦄ := by
  have hL0 : Tree.ModelsFrom hH self (0#usize).val l := by
    simpa [Tree.ModelsFrom, Tree.Models] using hL
  unfold Tree.proof
  step*

/-! ## Completeness -/

include hH in
/-- **Spec theorem for `examples::merkle::completeness`** -/
theorem completeness.spec (data : Slice (alloc.vec.Vec Std.U8)) (index : Std.Usize) :
    completeness H data index ⦃ b => b = true ⦄ := by
  unfold completeness
  step*
  have := innerRootF_proofFrom (nodeF hH) (data.val.map fun v => leafF hH v.deref) index.val
    (leafF hH v.deref)
    (by rw [List.getElem?_map, List.getElem?_eq_getElem (by scalar_tac), v_post]; rfl)
  have : m = data.len := by scalar_tac
  simp_all [innerF, alloc.vec.Vec.deref]
  scalar_tac

end Impl

/-- Completeness: for every lawful `H`, the honest proof for every leaf
verifies against the honest root. -/
public theorem completeness_spec {Hs D : Type _} (H : Hash Hs D) (hH : H.Lawful)
    (data : Slice (alloc.vec.Vec Std.U8)) (index : Std.Usize) :
    completeness H data index = ok true :=
  eq_ok_of_spec (completeness.spec hH data index)

end Completeness

end examples.merkle
