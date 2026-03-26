/-
  Joint observability: two “comparison” maps jointly separate points iff the product map is injective.
-/

import AdequacyArchitecture.Residual.Geometry

universe u

namespace AdequacyArchitecture.Residual

/-- Joint observability: paired maps `π₁ × π₂` are injective on `α`. -/
def JointObservable {α β γ : Type u} (π₁ : α → β) (π₂ : α → γ) : Prop :=
  Function.Injective (fun x => (π₁ x, π₂ x))

theorem jointObservable_of_left_injective {α β γ : Type u} (π₁ : α → β) (π₂ : α → γ)
    (h : Function.Injective π₁) : JointObservable π₁ π₂ := by
  intro x y hxy
  exact h (congrArg Prod.fst hxy)

end AdequacyArchitecture.Residual
