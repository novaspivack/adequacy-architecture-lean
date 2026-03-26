/-
  C2 — Residual geometry (abstract + Strata hooks).
  **Strata names (do not rename):** `vanishingCriterion`, `resolutionComplexityTheorem`,
  `predicateClassification` in `Universal/Residual/FundamentalTheorem.lean` (via `Strata.lean`).
-/

import AdequacyArchitecture.Residual.CanonicalCarrier

universe u

namespace AdequacyArchitecture.Residual

open ReflexiveArchitecture.Universal.Residual

variable {α β : Type u}

/-- Some pair lies in the universal forgetting kernel of `π` (nontrivial residual). -/
def kernelNonempty (π : α → β) : Prop :=
  ∃ p : α × α, p ∈ forgettingKernel π

/-- Bundle slot for geometry data; `residualGeometryOf` ties to Strata `forgettingKernel`. -/
structure ResidualGeometry (α : Type u) where
  nonemptyKernelWitness : Prop

/-- Geometry record induced by a comparison map `π : α → β`. -/
def residualGeometryOf (π : α → β) : ResidualGeometry α where
  nonemptyKernelWitness := kernelNonempty π

end AdequacyArchitecture.Residual
