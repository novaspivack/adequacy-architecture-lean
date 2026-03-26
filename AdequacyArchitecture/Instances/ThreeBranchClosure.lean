/-
  **SPEC_026 — Phase 4:** honest three-branch packaging into the summit framework.

  **No smuggled carrier identifications** (**`SPEC_014_UC1`**): NEMS+IC lawful **relocation/finality** lives on
  **`CorpusStrataCarrier`**; IC-native certification multiplicity lives on **`CompressionArchitecture Unit _`**; APS
  indexed **middle** lives on **`Unit`**. This module **packages** those three honest facts together — it does **not**
  claim `Fin 2 ≃ CompressionArchitecture` or a unified `HFinal` on all carriers.

  * **NEMS + IC (relocation/finality):** `icCS3HFinal` with `HFinalWithBranchRole.ofRelocationFinality`.
  * **IC (native joint):** `ic_faithful_native_pair_cs3_nv_bridge_core_joint` (corpus corridor NV row + IC fields).
  * **APS (composition/middle):** `minimalIndexedApsRealizationLayer` as a `Middle.RealizationLayer` witness — **not**
    an `HFinal Unit` (two-point relocation is obstructed on `Unit`; see `UnifiedCarrierMorphisms`).
-/

import AdequacyArchitecture.Instances.ICSummitRepresentation
import AdequacyArchitecture.Instances.ICBridgeCoreRecord
import AdequacyArchitecture.Instances.APSIndexedOuterClosure
import AdequacyArchitecture.Lawful.FinalConditionalSummit

namespace AdequacyArchitecture.Instances

open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open ReflexiveArchitecture

/--
Witness bundling **all three** branch families into one **theorem-fed** package (roles distinguished; carriers **not**
identified).
-/
structure ThreeBranchSummitClosureWitness where
  /-- Shared corpus **`HFinal`** for the NEMS/IC Fin 2 / corpus corridor row, tagged relocation/finality. -/
  nemsIcRelocationTagged : HFinalWithBranchRole CorpusStrataCarrier
  /-- IC-native joint bundle (SPEC_021 CS-3) beyond bare **`HFinal`**. -/
  icNativeJoint : ic_faithful_native_pair_cs3_nv_bridge_core_joint_prop
  /-- APS indexed middle (`SPEC_020` / Strata interface) at **`Unit`**. -/
  apsIndexedMiddle : Middle.RealizationLayer apsIndexedSummitMiddleCarrier

/-- Standard witness: corpus `icCS3HFinal`, IC joint theorem, minimal indexed APS middle. -/
def standardThreeBranchSummitClosureWitness : ThreeBranchSummitClosureWitness where
  nemsIcRelocationTagged := HFinalWithBranchRole.ofRelocationFinality icCS3HFinal
  icNativeJoint := ic_faithful_native_pair_cs3_nv_bridge_core_joint
  apsIndexedMiddle := minimalIndexedApsRealizationLayer

theorem three_branch_summit_closure_nonempty : Nonempty ThreeBranchSummitClosureWitness :=
  ⟨standardThreeBranchSummitClosureWitness⟩

/-- Layer-A cascade on the **corpus** relocation/finality spine carried in the standard witness. -/
theorem three_branch_corpus_highest_summit_at :
    MasterStratifiedAdequacyCascadeAt icCS3HFinal.𝔠 icCS3HFinal.P icCS3HFinal.rcp :=
  highestReachable_summit_at icCS3HFinal

/-- The tagged row unfolds to **`icCS3HFinal`**. -/
theorem standard_three_branch_relocation_is_icCS3 :
    standardThreeBranchSummitClosureWitness.nemsIcRelocationTagged.toHFinal = icCS3HFinal :=
  rfl

end AdequacyArchitecture.Instances
