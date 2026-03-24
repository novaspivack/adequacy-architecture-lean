/-
  Route architecture (schematic; strengthened in `Route/` band).
-/

import AdequacyArchitecture.Core.Account
import AdequacyArchitecture.Core.Adequacy

universe u

namespace AdequacyArchitecture

variable {α : Type u}

/-- Route data indexed by account (placeholder refine to fiber/refinement data).
    Named `RouteDatum` to avoid clashing with the `Route/` formalization band namespace. -/
structure RouteDatum (α : Type u) where
  feature : Account α → Prop

def RouteAdequate (P : AdequacyPredicates α) (m : AdeqMode) (r : RouteDatum α) : Prop :=
  ∀ A, r.feature A → P.adeq m A

end AdequacyArchitecture
