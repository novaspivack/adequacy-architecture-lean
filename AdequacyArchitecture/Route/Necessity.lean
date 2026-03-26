/-
  F2 — Route necessity (comparison injective ⇒ no bare collapse of distinct routes).
-/

import AdequacyArchitecture.Residual.Strata

universe u

namespace AdequacyArchitecture.Route

open ReflexiveArchitecture.Universal

def WeakRouteNecessity {α β : Type u} (π : α → β) : Prop :=
  MinimalExhaustive (Residual.rcsOfMap π)

end AdequacyArchitecture.Route
