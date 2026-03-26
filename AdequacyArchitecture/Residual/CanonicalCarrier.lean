/-
  C1 — Canonical residual carrier (abstract layer).
  **Strata:** `lakefile` `require`s `«reflexive-architecture»`; see `Residual/Strata.lean`
  and SPEC_001 (`rcsOfMap`, `ResidualKernel`, `forgettingKernel`).
-/

import AdequacyArchitecture.Core.Basic
import AdequacyArchitecture.Residual.Strata

open ReflexiveArchitecture.Universal

universe u v

namespace AdequacyArchitecture.Residual

variable {α β : Type u}

/-- Abstract comparison / projection (map-forgetting story). -/
abbrev CompareMap := α → β

/-- Strata packaging of a comparison map as an `RCS` (SPEC_001: `rcsOfMap`). -/
abbrev rcsOfCompareMap (f : α → β) : ReflectiveCertificationSystem β α :=
  ReflexiveArchitecture.Universal.Residual.rcsOfMap f

/-- Program-level tag; Strata residual kernel for `f` is `ResidualKernel (rcsOfCompareMap f)`. -/
structure ResidualWitness (α : Type u) where
  tag : CarrierTag

end AdequacyArchitecture.Residual
