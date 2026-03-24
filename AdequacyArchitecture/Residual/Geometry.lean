/-
  C2 — Residual geometry (abstract).
  **Strata names (do not rename):** `vanishingCriterion`, `resolutionComplexityTheorem`, `predicateClassification` in `Universal/Residual/FundamentalTheorem.lean`.
-/

import AdequacyArchitecture.Residual.CanonicalCarrier

universe u

namespace AdequacyArchitecture.Residual

/-- Bundle slot for geometry data (fiber decomposition, duality, complexity) — refine with Strata imports. -/
structure ResidualGeometry (α : Type u) where
  nonemptyKernelWitness : Prop

end AdequacyArchitecture.Residual
