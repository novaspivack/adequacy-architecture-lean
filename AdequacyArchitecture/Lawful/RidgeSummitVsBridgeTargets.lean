/-
  Alignment note: SPEC_010 (bridge **targets**) vs SPEC_011 (`RidgeSummitStatements`).

  * **Outer targets** (`BridgeTargets.lean`): second disjuncts are **canonical carrier tag**
    equalities (`CarrierTag.residual`, `CarrierTag.gluingObstruction`). B2 iff lemmas
    (`BridgeTheorems.lean`) show these disjuncts are **never** used under current
    `burdenCarrierTag = semanticRemainder` — so the targets reduce to pure “first branch”
    (negated repr-adequacy on `C A`, or `False` on the outer-to-middle chain).

  * **SPEC_011 bridges** (`RidgeSummitStatements.lean`): second disjuncts use **lawful hooks**
    (`InnerResidualInducedByCanonical`, `MiddleLayerWitnessCoversBurden`, …) — the intended
    substantive ridge statements once Strata/middle-layer refinements land.

  * **Cascade:** `MasterStratifiedAdequacyCascadeTarget` = old targets + `UniversalBurdenRelocationLawful`
    (S2 recast). `MasterStratifiedAdequacyCascade` = SPEC_011 five conjuncts including
    `RouteConstraintProfile` and `NonFlatFinalityFromRouteConstraint`.
-/

import AdequacyArchitecture.Lawful.BridgeTargets
import AdequacyArchitecture.Lawful.RidgeSummitStatements
