/-
  C4 — Recovery / refinement duality (abstract).

  **Strata:** per-fiber resolution / complexity: `resolutionComplexityTheorem`,
  `resolves_iff_separates_all_kernel_pairs` (`Residual` / `FundamentalTheorem`, imported via `Residual/Strata.lean`).
-/

import AdequacyArchitecture.Core.Basic

universe u

namespace AdequacyArchitecture.Residual

/-- Minimal recovery invariant slot (refine using Strata `Refinement` + Adequacy `Account`). -/
structure RecoveryInvariant (α : Type u) where
  minRefinement : Account α → Prop

end AdequacyArchitecture.Residual
