/-
  C3 — Burden composition along composable maps (abstract).

  **Strata:** functorial kernel transport is `compatible_preserves_kernel` /
  `compCompatible` in `ReflexiveArchitecture.Universal.Residual.ResidualKernel` (import via `Residual/Strata.lean` + Residual barrel).
-/

import AdequacyArchitecture.Residual.CanonicalCarrier

universe u

namespace AdequacyArchitecture.Residual

variable {α β γ : Type u}

def composable (f : α → β) (g : β → γ) : α → γ := g ∘ f

/-- Composition obstruction slot (Adequacy-native theorem TBD; Strata supplies RCS-compatible maps). -/
structure CompositionObstruction (α β γ : Type u) where
  witness : Prop

end AdequacyArchitecture.Residual
