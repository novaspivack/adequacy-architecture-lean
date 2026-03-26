/-
  **SPEC_026 — Phase 2 (APS indexed closure).**

  APS must **not** be forced through the NEMS/IC **two-point relocation** pattern: native `Unit` blocks that
  witness geometry (`UnifiedCarrierMorphisms.not_exists_distinct_pair_unit`). The honest carrier story is the
  **indexed** middle layer (**`APSIndexedFaithful`**) — tracking/gluing/interpolation exactness — i.e. a
  **composition / obstruction** role relative to relocation/finality.

  **Delivered (COMPLETE — SPEC_026 §3):** **`aps_indexed_middle_tracking_and_gluing_of_icomp`**,
  **`aps_indexed_icomp_of_tracking_and_gluing`**, and **`aps_indexed_summit_engine_agrees_middle`**
  (**SPEC_020** `summit_engine_composition_from_gluing` **defeq** Strata `composition_from_tracking_and_gluing` on
  **`indexedApsRealizationLayer`**).

  **Not claimed:** `HFinal Unit` or Fin-2 relocation for APS (SPEC_026 §8).
-/

import AdequacyArchitecture.Instances.APSIndexedFaithful
import AdequacyArchitecture.Summit.SummitEngine
import APSMinimalInterface.Indexed
import APSMinimalInterface.InterfaceLattice
import APSRecComp.ConditionalNecessity
import APSUniformization.Synthesis

namespace AdequacyArchitecture.Instances

open APSMinimalInterface
open APSRecComp
open APSUniformization
open ReflexiveArchitecture
open ReflexiveArchitecture.Middle
open AdequacyArchitecture.Summit

/-- Phase-2 summit **middle** carrier index: same as **`APSFaithful`** / indexed realization layer (`Unit`). -/
abbrev apsIndexedSummitMiddleCarrier : Type := Unit

theorem aps_indexed_middle_tracking_and_gluing_of_icomp (aps : IndexedAPS) (hI : HasICompIndexed aps) :
    let M := indexedApsRealizationLayer aps
    M.HasFiniteTracking ∧ M.HasGluing :=
  (aps_interpolation_exactness aps).mp hI

/-- `HasICompIndexed` from finite tracking + gluing (**reverse** of **`aps_indexed_middle_tracking_and_gluing_of_icomp`**). -/
theorem aps_indexed_icomp_of_tracking_and_gluing (aps : IndexedAPS) (h : HasFiniteTracking aps ∧ HasGluing aps) :
    HasICompIndexed aps :=
  (aps_interpolation_exactness aps).mpr h

/--
**Phase 2 — APS enters via SPEC_020 summit engine:** on `indexedApsRealizationLayer aps`, the Adequacy
**`summit_engine_composition_from_gluing`** is **definitionally** the Strata **`composition_from_tracking_and_gluing`**
(same mathematical content — honest middle-layer path, not Fin-2 relocation).
-/
theorem aps_indexed_summit_engine_agrees_middle (aps : IndexedAPS) (h : HasFiniteTracking aps ∧ HasGluing aps) :
    @summit_engine_composition_from_gluing Unit (indexedApsRealizationLayer aps) h =
      @composition_from_tracking_and_gluing Unit (indexedApsRealizationLayer aps) h :=
  rfl

end AdequacyArchitecture.Instances
