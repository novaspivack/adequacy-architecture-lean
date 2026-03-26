/-
  **SPEC_029_FR1 — FE-1 v1 (COMPLETE):** names SPEC_026’s **heterogeneous** native carriers for
  three-branch closure — **no** identifications (**`SPEC_014_UC1`**). This is bookkeeping for “native branch
  completion at scale”: additional corridors and hosts extend **this chart**, they do not collapse it.

  **Standard summit packaging:** **`ThreeBranchSummitClosureWitness`** (`Instances/ThreeBranchClosure.lean`).
-/

import AdequacyArchitecture.Instances.ThreeBranchClosure
import AdequacyArchitecture.Instances.CorpusDischarge
import AdequacyArchitecture.Instances.ICNativeOuterClosure
import AdequacyArchitecture.Instances.APSIndexedOuterClosure
import InfinityCompression.Meta.NEMSSpineAsArchitecture

namespace AdequacyArchitecture.Portability

open AdequacyArchitecture.Instances
open ReflexiveArchitecture
open InfinityCompression.Meta

universe u

/-- **FE-1:** explicit **four-type** carrier chart (corpus row + two IC-native compression hosts + APS middle).
    `ThreeBranchSummitClosureWitness` bundles **three** branch-shaped obligations; the IC spine uses **two**
    `CompressionArchitecture` indices. -/
structure FE1_StandardNativeCarrierChart : Type (u + 1) where
  nemsIcSummitCarrier : Type u
  icNativeCanonicalHost : Type u
  icNativeAltHost : Type u
  apsMiddleCarrier : Type u

/-- The repository’s **standard** native chart (**SPEC_026** / **SPEC_029** FE-1). -/
def fe1_standardNativeCarrierChart : FE1_StandardNativeCarrierChart where
  nemsIcSummitCarrier := CorpusStrataCarrier
  icNativeCanonicalHost := CompressionArchitecture Unit nemsSpineChain.steps.length
  icNativeAltHost := CompressionArchitecture Unit nemsSpineChain_altTerminal.steps.length
  apsMiddleCarrier := apsIndexedSummitMiddleCarrier

theorem fe1_chart_nemsIc_eq_corpus : fe1_standardNativeCarrierChart.nemsIcSummitCarrier = CorpusStrataCarrier := rfl

theorem fe1_chart_ic_canonical_eq :
    fe1_standardNativeCarrierChart.icNativeCanonicalHost = CompressionArchitecture Unit nemsSpineChain.steps.length :=
  rfl

/-- **FE-1:** canonical IC host in the standard chart is **`SPEC_026` Phase-1** **`icNemsSpineCompressionCarrier`**. -/
theorem fe1_chart_ic_canonical_eq_icNemsSpineCompressionCarrier :
    fe1_standardNativeCarrierChart.icNativeCanonicalHost = icNemsSpineCompressionCarrier :=
  rfl

theorem fe1_chart_ic_alt_eq :
    fe1_standardNativeCarrierChart.icNativeAltHost =
      CompressionArchitecture Unit nemsSpineChain_altTerminal.steps.length :=
  rfl

theorem fe1_chart_aps_eq_indexed_unit : fe1_standardNativeCarrierChart.apsMiddleCarrier = apsIndexedSummitMiddleCarrier :=
  rfl

/-- **FE-1** entry point: the **SPEC_026** three-branch witness is **inhabited** (same fact as
    **`three_branch_summit_closure_nonempty`**). -/
theorem fe1_three_branch_summit_closure_nonempty : Nonempty ThreeBranchSummitClosureWitness :=
  three_branch_summit_closure_nonempty

end AdequacyArchitecture.Portability
