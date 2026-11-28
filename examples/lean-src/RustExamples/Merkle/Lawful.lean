module

public import RustExamples.Gen.Funs

/-! Assumptions about the `Hash` implementation that the Merkle proofs rely on.

The Rust trait methods become fields of `merkle.Hash`, each returning a
`Result`. The proofs need the hash functions to never fail, and `==` and `!=`
on digests to decide equality. Nothing else is assumed about `H`; in
particular, collision resistance is not an assumption: binding is stated as
"either the proofs agree, or we can exhibit a collision".
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace examples.merkle

open Classical in
/-- A `Hash` implementation whose functions are total and whose digest
equality is real equality. -/
structure Hash.Lawful {Hs : Type _} {D : Type _} (H : Hash Hs D) : Prop where
  leaf_ok : ∀ s, ∃ d, H.leaf s = ok d
  node_ok : ∀ a b, ∃ d, H.node a b = ok d
  size_ok : ∀ a n, ∃ d, H.size a n = ok d
  eq_ok : ∀ a b : D, H.corecmpEqInst.partialEqInst.eq a b = ok (decide (a = b))
  ne_ok : ∀ a b : D, H.corecmpEqInst.partialEqInst.ne a b = ok (decide (a ≠ b))

/-- The extracted Rust predicate has exactly the assumptions used by the proofs. -/
theorem lawful_hash_iff {Hs D : Type _} (H : Hash Hs D) :
    (lawful_hash H).holds ↔ H.Lawful := by
  classical
  let returns (m : Result D) := ∃ d, (Aeneas.Std.bind m fun x => ok (x = d)).holds
  let decides (m : Result Bool) (p : Prop) := (do let b ← m; ok ((b = true) = p)).holds
  have total (m : Result D) : returns m ↔ ∃ d, m = ok d := by
    cases m <;> simp [returns, Result.holds, HaxProp.truth]
  have correct (m : Result Bool) (p : Prop) : decides m p ↔ m = ok (decide p) := by
    cases m with
    | ret b => cases b <;> by_cases hp : p <;> simp [decides, Result.holds, HaxProp.truth, hp]
    | _ => simp [decides, Result.holds]
  -- Unfold the five Rust quantifiers and their extracted closure bodies.
  simp only [lawful_hash, hax_lib.prop.constructors.forall, hax_lib.prop.constructors.and,
    bind_ok, Result.holds_ok, HaxProp.truth, id_eq, Prod.forall]
  simp only [lawful_hash.closure.Insts.CoreOpsFunctionFnTupleShared0SliceU8Prop.call,
    lawful_hash.closure_1.Insts.CoreOpsFunctionFnTuplePairProp.call,
    lawful_hash.closure_2.Insts.CoreOpsFunctionFnTuplePairClause0_DigestUsizeProp.call,
    lawful_hash.closure_3.Insts.CoreOpsFunctionFnTuplePairProp.call,
    lawful_hash.closure_4.Insts.CoreOpsFunctionFnTuplePairProp.call,
    hax_lib.prop.constructors.exists, hax_lib.prop.constructors.eq,
    hax_lib.prop.constructors.from_bool, hax_lib.prop.constructors.not,
    bind_ok, Result.holds_ok, HaxProp.truth, id_eq]
  change ((∀ s, returns (H.leaf s)) ∧ (∀ a b, (ok (returns (H.node a b))).holds)) ∧
    (∀ a n, (ok (returns (H.size a n))).holds) ∧
    (∀ a b, decides (H.corecmpEqInst.partialEqInst.eq a b) (a = b)) ∧
    (∀ a b, decides (H.corecmpEqInst.partialEqInst.ne a b) (a ≠ b)) ↔ _
  simp only [Result.holds_ok, HaxProp.truth, id_eq, total, correct]
  constructor
  · rintro ⟨⟨hl, hn⟩, hs, he, hne⟩
    refine ⟨hl, hn, hs, he, fun a b => ?_⟩
    by_cases e : a = b <;> simpa [e] using hne a b
  · intro h
    refine ⟨⟨h.leaf_ok, h.node_ok⟩, h.size_ok, h.eq_ok, fun a b => ?_⟩
    by_cases e : a = b <;> simpa [e] using h.ne_ok a b

end examples.merkle
