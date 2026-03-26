/-
  Summit S2 — raw `RouteDatum` target (may trivialize via `feature := fun _ => True`).

  **Lawful** summit shape: `AdequacyArchitecture.Lawful.UniversalBurdenRelocationLawful` (requires `LawfulRouteDatum`).
-/

import AdequacyArchitecture.Core.Basic
import AdequacyArchitecture.Core.Route
import AdequacyArchitecture.Burden.RelocationClass

-- `RouteDatum` from `Core/Route` (not the `Route/` band).

universe u

namespace AdequacyArchitecture.Summit

open AdequacyArchitecture.Burden (RelocationPair)

variable {α : Type u}

/-- **Summit target (not proved here):** relocation along `f` forces a route datum witnessing both endpoints. -/
def UniversalBurdenRelocationConjecture : Prop :=
  ∀ (B : BurdenPredicates α) (f : Transform α) (m₁ m₂ : BurdenMode) (A : Account α),
    RelocationPair B m₁ m₂ f A → ∃ r : RouteDatum α, r.feature A ∧ r.feature (f A)

end AdequacyArchitecture.Summit
