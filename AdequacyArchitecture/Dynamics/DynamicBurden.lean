/-
  E1 — Dynamic burden: nontrivial fiber / residual along a comparison map.
-/

import AdequacyArchitecture.Dynamics.ContinuationAdequacy

universe u

namespace AdequacyArchitecture.Dynamics

open ReflexiveArchitecture.Universal

/-- Dynamic burden witness: **non-exhaustive** comparison (distinct points share a certificate). -/
def dynamicBurdenWitness {α β : Type u} (π : α → β) : Prop :=
  NonExhaustive (Residual.rcsOfMap π)

theorem nonExhaustive_of_not_continuation_adequate {α β : Type u} (π : α → β)
    (h : ¬ ContinuationAdequate π) : dynamicBurdenWitness π := by
  dsimp [ContinuationAdequate, dynamicBurdenWitness] at h ⊢
  exact (nonExhaustive_iff_not_minimal (S := Residual.rcsOfMap π)).mpr h

end AdequacyArchitecture.Dynamics
