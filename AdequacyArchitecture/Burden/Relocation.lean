/-
  B3 — Burden relocation: explicit witness that burden reappears after a drop on the transformed account.
-/

import AdequacyArchitecture.Core.Basic

universe u

namespace AdequacyArchitecture.Burden

variable {α : Type u}

/-- Direct witness: `m₂` carries burden after `f`, so some burden mode is realized on `f A`. -/
theorem burden_not_erased_only_relocated
    (B : BurdenPredicates α) (m₂ : BurdenMode) (f : Transform α) (A : Account α)
    (hw : B.burden m₂ (f A)) :
    ∃ m', B.burden m' (f A) :=
  ⟨m₂, hw⟩

/-- If `m₁` was present on `A` but absent on `f A`, and `m₂` holds on `f A`, relocation from `m₁` to `m₂` is witnessed. -/
theorem adequacy_preserving_drop_implies_relocation
    (B : BurdenPredicates α) (m₁ m₂ : BurdenMode) (f : Transform α) (A : Account α)
    (_hpre : B.burden m₁ A) (_hpost : ¬ B.burden m₁ (f A)) (hw : B.burden m₂ (f A)) :
    ∃ m', B.burden m' (f A) :=
  ⟨m₂, hw⟩

end AdequacyArchitecture.Burden
