/-
  C3 — Burden composition along composable maps (abstract).
-/

import AdequacyArchitecture.Residual.CanonicalCarrier

universe u

namespace AdequacyArchitecture.Residual

variable {α β γ : Type u}

def composable (f : α → β) (g : β → γ) : α → γ := g ∘ f

/-- Composition obstruction slot (refine to `ResidualProgram` compositional lemmas). -/
structure CompositionObstruction (α β γ : Type u) where
  witness : Prop

end AdequacyArchitecture.Residual
