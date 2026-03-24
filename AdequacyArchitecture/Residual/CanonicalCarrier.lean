/-
  C1 — Canonical residual carrier (abstract layer).
  **Strata alignment:** import `ReflexiveArchitecture.Universal.Residual.*` and `UniversalForgetting` when `lakefile` wires `reflexive-architecture-lean` (see SPEC_001).
-/

import AdequacyArchitecture.Core.Basic

universe u v

namespace AdequacyArchitecture.Residual

variable {α β : Type u}

/-- Abstract comparison / projection (map-forgetting story). -/
abbrev CompareMap := α → β

/-- Placeholder residual witness until Strata `ResidualKernel` is imported. -/
structure ResidualWitness (α : Type u) where
  tag : CarrierTag

end AdequacyArchitecture.Residual
