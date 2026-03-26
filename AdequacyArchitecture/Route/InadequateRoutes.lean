/-
  Counterforms: flat / burden-hiding routes — non-injective comparison.
-/

import AdequacyArchitecture.Residual.Strata

universe u

namespace AdequacyArchitecture.Route

open ReflexiveArchitecture.Universal

def FlatRouteInadequate {α β : Type u} (π : α → β) : Prop :=
  NonExhaustive (Residual.rcsOfMap π)

end AdequacyArchitecture.Route
