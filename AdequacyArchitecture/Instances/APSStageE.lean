/-
  **SPEC_030_MX7 — Stage E (APS rightful role).**

  APS enters the summit program through the **SPEC_020** middle band — **finite tracking ∧ gluing ⇒ `ICompIdx`**
  on **`Middle.RealizationLayer Unit`** — **not** through a **`HFinal Unit`** / Fin-2 relocation corridor (obstructed:
  **`UnifiedCarrierMorphisms.not_exists_distinct_pair_faithful_aps_middle`**).

  **Positive spine (theorem-fed):** the **standard** indexed APS **`stdAPS`** satisfies **`HasICompIndexed`**
  (**`APSRecComp.StandardComparison.standard_recursion_interface_implies_I_comp`**), hence the **interpolation
  exactness** biconditional yields **`HasFiniteTracking ∧ HasGluing`**, and **`summit_engine_composition_from_gluing`**
  proves **`ICompIdx`** on **`indexedApsRealizationLayer stdAPS`**.

  **Sharp obstruction (minimal countermodel):** **`minimalIndexedAPS`** has **`¬ HasICompIndexed`**
  (**`IndexedCountermodels.minimalIndexed_no_comp`**), hence **no** conjunction **`HasFiniteTracking ∧
  HasGluing`** — the **three-branch** packaging witness **`minimalIndexedApsRealizationLayer`** is still a valid
  **`Middle.RealizationLayer`**, but it **cannot** fire the summit engine.

  **Certified row:** a **`CertifiedFrontierRow Unit`** would still require **`Nonempty (HFinal Unit)`** via
  **`nonempty_certifiedFrontierRow_implies_nonempty_hfinal`**; this module does **not** construct that — the honest APS
  contribution is the **middle contract** + (**`APSFe2MiddleTransport`**) FE-3 **`Core`** story, not relocation.
-/

import APSMinimalInterface.IndexedCountermodels
import APSMinimalInterface.StandardAPS
import APSRecComp.StandardComparison
import AdequacyArchitecture.Instances.APSFe2MiddleTransport
import AdequacyArchitecture.Instances.APSIndexedFaithful
import AdequacyArchitecture.Instances.APSIndexedOuterClosure
import AdequacyArchitecture.LocalGlobal.GluingObstruction
import AdequacyArchitecture.Portability.CertifiedFrontierRow
import AdequacyArchitecture.Summit.SummitEngine

namespace AdequacyArchitecture.Instances

open AdequacyArchitecture.LocalGlobal
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open AdequacyArchitecture.Portability
open AdequacyArchitecture.Summit
open APSMinimalInterface
open APSRecComp
open APSUniformization

/-! ## Stage E — standard indexed APS: middle-role summit engine path -/

/-- Finite tracking + gluing for **`stdAPS`**, from **`HasICompIndexed`** + interpolation exactness. -/
theorem aps_stageE_std_finite_tracking_and_gluing :
    HasFiniteTracking stdAPS ∧ HasGluing stdAPS :=
  (aps_interpolation_exactness stdAPS).mp standard_recursion_interface_implies_I_comp

/--
**SPEC_020 / SPEC_026 Phase-2 conclusion** on the **standard** indexed middle host: the engine yields **`ICompIdx`**
(**proof content** — not a `HFinal` row).
-/
theorem aps_stageE_std_summit_engine_yields_icomp :
    (indexedApsRealizationLayer stdAPS).ICompIdx :=
  @summit_engine_composition_from_gluing Unit (indexedApsRealizationLayer stdAPS)
    aps_stageE_std_finite_tracking_and_gluing

/-- Same identity as **`aps_indexed_summit_engine_agrees_middle`** — **SPEC_030** name for the standard APS instance. -/
theorem aps_stageE_std_summit_engine_agrees_middle :
    @summit_engine_composition_from_gluing Unit (indexedApsRealizationLayer stdAPS)
        aps_stageE_std_finite_tracking_and_gluing =
      @composition_from_tracking_and_gluing Unit (indexedApsRealizationLayer stdAPS)
        aps_stageE_std_finite_tracking_and_gluing :=
  aps_indexed_summit_engine_agrees_middle stdAPS aps_stageE_std_finite_tracking_and_gluing

/-! ## FE-3 middle transport alignment (`R := Prop`, phantom `Unit`) -/

theorem aps_stageE_std_agreed_summit_prop_eq_layer_icompidx :
    apsUnitMiddleBranchGenericCore.ops.agreedSummit (indexedApsRealizationLayer stdAPS) =
      (indexedApsRealizationLayer stdAPS).ICompIdx :=
  rfl

/-! ## Sharp obstruction — minimal indexed APS cannot supply engine hypotheses -/

theorem aps_stageE_minimal_not_finite_tracking_and_gluing :
    ¬ (HasFiniteTracking minimalIndexedAPS ∧ HasGluing minimalIndexedAPS) := fun h =>
  minimalIndexed_no_comp ((aps_interpolation_exactness minimalIndexedAPS).2 h)

/-! ## Certified frontier row (obstruction context) -/

theorem aps_stageE_certifiedFrontierRow_unit_implies_nonempty_hfinal :
    Nonempty (CertifiedFrontierRow Unit) → Nonempty (HFinal Unit) :=
  nonempty_certifiedFrontierRow_implies_nonempty_hfinal

end AdequacyArchitecture.Instances
