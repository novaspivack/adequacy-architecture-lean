/-
  Phase 2 — Strata (Reflexive Architecture) residual spine.

  Single import hub for `ReflexiveArchitecture.Universal.Residual.*` used by
  Adequacy bands. Verified theorem and definition names are declared in this residual spine and in
  `Residual/CanonicalCarrier.lean`.

  `UniversalForgetting` pulls in `FundamentalTheorem` (paper aliases
  `vanishingCriterion`, `resolutionComplexityTheorem`, `predicateClassification`)
  and the universal `rcsOfMap` / `forgettingKernel` API.
-/

import ReflexiveArchitecture.Universal.Residual.UniversalForgetting
