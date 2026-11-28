module

public import Aeneas

/-! The hax backend calls the Aeneas result monad `RustM`. Interpret its
specification primitives in the repository's Aeneas library. A quantified
body holds only if evaluating it returns a true proposition. The constructors
follow [the pinned hax model](https://github.com/pereq-dev/hax/blob/0d2f66ed697c46d7c0f5038150b7c9679e4d954b/hax-lib/proof-libs/lean/CoreModels/HaxLib/Prop.lean).
-/

@[expose] public section
open Aeneas Aeneas.Std Result

namespace Aeneas.Std
abbrev RustM := Result
namespace RustM
export Aeneas.Std.Result (ok fail)
end RustM

class HaxProp (α : Type) where
  truth : α → Prop

instance : HaxProp Prop := ⟨id⟩
instance : HaxProp Bool := ⟨fun b => b = true⟩

def Result.holds {α : Type} [HaxProp α] (m : Result α) : Prop :=
  m ⦃ p => HaxProp.truth p ⦄

@[simp] theorem Result.holds_ok {α : Type} [HaxProp α] (p : α) :
    (Result.ok p).holds ↔ HaxProp.truth p := by simp [Result.holds]

end Aeneas.Std

namespace hax_lib.prop
abbrev «Prop» := Prop
namespace constructors
def from_bool (b : Bool) : Result Prop := ok (b = true)
def and (p q : Prop) : Result Prop := ok (p ∧ q)
def not (p : Prop) : Result Prop := ok (¬ p)
def eq {α : Type u} (a b : α) : Result Prop := ok (a = b)
def «forall» {α : Type u} {F : Type v} (fn : core.ops.function.Fn F α Prop) (f : F) : Result Prop :=
  ok (∀ x, (fn.call f x).holds)
def «exists» {α : Type u} {F : Type v} (fn : core.ops.function.Fn F α Prop) (f : F) : Result Prop :=
  ok (∃ x, (fn.call f x).holds)
end constructors
end hax_lib.prop
