/-
  Relocation carrier class (registry placeholder; strengthen with `Structure`/`Class` as instances land).
-/

import AdequacyArchitecture.Core.Basic

universe u

namespace AdequacyArchitecture.Burden

variable {α : Type u}

/-- Predicate: `m₂` is an admissible relocation target for mode `m₁` under transform `f`. -/
def RelocationPair (B : BurdenPredicates α) (m₁ m₂ : BurdenMode) (f : Transform α) (A : Account α) : Prop :=
  B.burden m₁ A ∧ ¬ B.burden m₁ (f A) ∧ B.burden m₂ (f A)

end AdequacyArchitecture.Burden
