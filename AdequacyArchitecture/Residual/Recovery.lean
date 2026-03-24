/-
  C4 — Recovery / refinement duality (abstract).
-/

import AdequacyArchitecture.Core.Basic

universe u

namespace AdequacyArchitecture.Residual

/-- Minimal recovery invariant slot (ties to Strata `resolutionComplexityTheorem` when wired). -/
structure RecoveryInvariant (α : Type u) where
  minRefinement : Account α → Prop

end AdequacyArchitecture.Residual
