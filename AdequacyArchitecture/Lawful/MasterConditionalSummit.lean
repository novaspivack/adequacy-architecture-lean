/-
  SPEC_021_Q9K — **CS-1** master conditional interface: explicit `H(𝔠)` shapes and packaged conclusions.

  * **`RidgeCascadeWitness 𝔠`** — the intended **hypothesis bundle** `H(𝔠)` for the SPEC_011 **ridge** segment
    (`MasterStratifiedAdequacyCascadeRidgeAt`).
  * **`RidgeBridgeable 𝔠`** — lighter **structural** hypothesis; yields `CarrierPatternInducesRouteConstraintAt` alone.

  No quantification over all `𝔠`; every `∀ …` theorem in this band is **prefixed** by these documented hypotheses.
-/

import AdequacyArchitecture.Lawful.RidgeBridgeable
import AdequacyArchitecture.Lawful.ConditionalSummit

universe u

namespace AdequacyArchitecture.Lawful

variable {α : Type u}

/-- From **`H(𝔠) := RidgeCascadeWitness 𝔠`**, the master **ridge** cascade holds (`SPEC_021` CS-1). -/
theorem master_conditional_summit_ridge_at
    {𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α} (h : RidgeCascadeWitness 𝔠) :
    MasterStratifiedAdequacyCascadeRidgeAt 𝔠 :=
  conditional_master_stratified_ridge_at_of_witness h

theorem master_conditional_route_constraint_at_of_ridgeBridgeable
    {𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α} (h : RidgeBridgeable 𝔠) :
    CarrierPatternInducesRouteConstraintAt 𝔠 :=
  carrierPatternInducesRouteConstraintAt_of_ridgeBridgeable h

/--
**SPEC_029 FE-4 (generic conditional, Layer A shape):** **`RidgeCascadeWitness 𝔠`** + **`NonFlatFinalityFromRouteConstraintFor P rcp`**
packages **`MasterStratifiedAdequacyCascadeAt 𝔠 P rcp`** — same_conjuncts as **`HFinal.mk …` sans `HFinal` bundle**.
**`RidgeBridgeable`** alone is **insufficient** (only the route-constraint ridge conjunct is forced); see
**`partial_route_and_nonFlat_of_ridgeBridgeable`**.
-/
theorem masterStratifiedAdequacyCascadeAt_of_ridgeCascadeWitness_and_nonFlat
    {𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α} {P : AdequacyPredicates α}
    {rcp : RouteConstraintProfile α} (w : RidgeCascadeWitness 𝔠)
    (nf : NonFlatFinalityFromRouteConstraintFor P rcp) :
    MasterStratifiedAdequacyCascadeAt 𝔠 P rcp :=
  And.intro (master_conditional_summit_ridge_at w) nf

/--
**Hypothesis minimization (Layer A, fixed `𝔠, P,rcp`):** `MasterStratifiedAdequacyCascadeAt` is **exactly**
ridge-at **plus** pointwise non-flat — and ridge-at is **definitionally equivalent** to `RidgeCascadeWitness`
(`ridgeCascadeWitness_iff_masterStratifiedAdequacyCascadeRidgeAt`).
So **`RidgeBridgeable` + non-flat** cannot be strengthened to this conclusion without the **remaining three**
bridge conjuncts (**`FinalConditionalSummit.partial_route_and_nonFlat_of_ridgeBridgeable`** stops at route + non-flat).
-/
theorem masterStratifiedAdequacyCascadeAt_iff_ridgeCascadeWitness_and_nonFlat
    (𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α) (P : AdequacyPredicates α)
    (rcp : RouteConstraintProfile α) :
    MasterStratifiedAdequacyCascadeAt 𝔠 P rcp ↔
      RidgeCascadeWitness 𝔠 ∧ NonFlatFinalityFromRouteConstraintFor P rcp :=
  Iff.intro
    (fun h =>
      And.intro (ridgeCascadeWitness_of_masterStratifiedAdequacyCascadeRidgeAt h.1) h.2)
    (fun h =>
      And.intro (masterStratifiedAdequacyCascadeRidgeAt_of_ridgeCascadeWitness h.1) h.2)

end AdequacyArchitecture.Lawful
