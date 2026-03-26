/-
  F1 — Route burden: nontrivial residual along the route’s comparison map.
-/

import AdequacyArchitecture.Residual.Strata

universe u

namespace AdequacyArchitecture.Route

open ReflexiveArchitecture.Universal

def RouteBurdenWitness {α β : Type u} (π : α → β) : Prop :=
  NonExhaustive (Residual.rcsOfMap π)

end AdequacyArchitecture.Route
