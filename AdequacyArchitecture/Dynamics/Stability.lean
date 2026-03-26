/-
  Stability: injective comparison (alias of minimal exhaustion for a map-as-RCS).
-/

import AdequacyArchitecture.Residual.Strata

universe u

namespace AdequacyArchitecture.Dynamics

open ReflexiveArchitecture.Universal

def StabilityPredicate {α β : Type u} (π : α → β) : Prop :=
  MinimalExhaustive (Residual.rcsOfMap π)

theorem stability_iff_injective {α β : Type u} (π : α → β) :
    StabilityPredicate π ↔ Function.Injective π := by
  simp [StabilityPredicate, MinimalExhaustive, Residual.rcsOfMap]

end AdequacyArchitecture.Dynamics
