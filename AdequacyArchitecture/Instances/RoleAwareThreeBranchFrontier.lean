/-
  **SPEC_030_MX7 — Stage F (v1):** role-aware **three-branch frontier** packaging.

  **Honesty:** this is **not** a single `HFinal` shared by all carriers (**`SPEC_014_UC1`**). It **is** one
  theorem-backed record tying:

  * **NEMS** — corpus `HFinal` tagged **`relocationFinality`** (Fin-2 corridor / outer spine story);
  * **IC** — **same** `HFinal` tagged **`certificationRepresentation`** (**metadata** — IC-native joint bundle is
    separate proof data), plus the CS-3 **`ic_faithful_native_pair_cs3_nv_bridge_core_joint`** proposition;
  * **APS** — **standard** indexed middle **`stdAPS`** **`ICompIdx`** via **`aps_stageE_std_summit_engine_yields_icomp`**
    (**composition / gluing** — not `HFinal Unit`).

  **vs `ThreeBranchSummitClosureWitness`:** Stage F keeps the **legacy** middle witness **`minimalIndexedAPS`**
  in **`standardThreeBranchSummitClosureWitness`** for **nonemptiness**, but the **engine-ready** APS path is
  **`stdAPS`** (**`APSStageE`**).
-/

import APSMinimalInterface.StandardAPS
import AdequacyArchitecture.Instances.APSIndexedFaithful
import AdequacyArchitecture.Instances.APSStageE
import AdequacyArchitecture.Instances.ICBridgeCoreRecord
import AdequacyArchitecture.Instances.ICSummitRepresentation
import AdequacyArchitecture.Lawful.FinalConditionalSummit
import AdequacyArchitecture.Portability.CertifiedFrontierRow
import AdequacyArchitecture.Portability.GenericSemanticSummitLift
import AdequacyArchitecture.Summit.SummitBranchRoles

namespace AdequacyArchitecture.Instances

open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open AdequacyArchitecture.Portability
open AdequacyArchitecture.Portability.BranchGenericSemanticTransport
open AdequacyArchitecture.Summit
open APSMinimalInterface

/-- **`icCS3HFinal`** under the IC certification / representation role (**tag only**). -/
def icCS3HFinalCertificationTagged : HFinalWithBranchRole CorpusStrataCarrier :=
  HFinalWithBranchRole.ofCertificationRepresentation icCS3HFinal

/--
**SPEC_030 Stage F v1** — three honest branch modes at once: NEMS relocation tag, IC certification tag + native
joint bundle, APS standard middle **`ICompIdx`**.
-/
structure RoleAwareThreeBranchFrontierPackage where
  /-- NEMS read: relocation / finality. -/
  nemsRelocationTagged : HFinalWithBranchRole CorpusStrataCarrier
  nemsRelocationRole : nemsRelocationTagged.branchRole = SummitBranchRole.relocationFinality
  /-- IC read: certification / native-vs-represented (**same `HFinal` as `nemsRelocationTagged`**). -/
  icCertificationTagged : HFinalWithBranchRole CorpusStrataCarrier
  icCertificationRole : icCertificationTagged.branchRole = SummitBranchRole.certificationRepresentation
  sameHFinal : nemsRelocationTagged.toHFinal = icCertificationTagged.toHFinal
  icNativeJoint : ic_faithful_native_pair_cs3_nv_bridge_core_joint_prop
  apsStdMiddleIComp : (indexedApsRealizationLayer stdAPS).ICompIdx

/-- Preferred standard package: **`icCS3HFinal`** with both tags; CS-3 joint; **`stdAPS`** engine conclusion. -/
def standardRoleAwareThreeBranchFrontierPackage : RoleAwareThreeBranchFrontierPackage where
  nemsRelocationTagged := HFinalWithBranchRole.ofRelocationFinality icCS3HFinal
  nemsRelocationRole := rfl
  icCertificationTagged := icCS3HFinalCertificationTagged
  icCertificationRole := rfl
  sameHFinal := rfl
  icNativeJoint := ic_faithful_native_pair_cs3_nv_bridge_core_joint
  apsStdMiddleIComp := aps_stageE_std_summit_engine_yields_icomp

theorem role_aware_three_branch_frontier_nonempty : Nonempty RoleAwareThreeBranchFrontierPackage :=
  ⟨standardRoleAwareThreeBranchFrontierPackage⟩

theorem standard_role_aware_nems_tag_eq_relocationFinality :
    standardRoleAwareThreeBranchFrontierPackage.nemsRelocationTagged.branchRole =
      SummitBranchRole.relocationFinality :=
  rfl

theorem standard_role_aware_ic_tag_eq_certificationRepresentation :
    standardRoleAwareThreeBranchFrontierPackage.icCertificationTagged.branchRole =
      SummitBranchRole.certificationRepresentation :=
  rfl

theorem standard_role_aware_icomp_eq_engine_proof :
    standardRoleAwareThreeBranchFrontierPackage.apsStdMiddleIComp =
      aps_stageE_std_summit_engine_yields_icomp :=
  rfl

/-! ## Stage G — consequence bundle from a role-aware witness -/

theorem roleAwareFrontierPackage_corpus_relocation_master_cascade
    (w : RoleAwareThreeBranchFrontierPackage) :
    MasterStratifiedAdequacyCascadeAt w.nemsRelocationTagged.toHFinal.𝔠 w.nemsRelocationTagged.toHFinal.P
      w.nemsRelocationTagged.toHFinal.rcp :=
  highestReachable_summit_at w.nemsRelocationTagged.toHFinal

/-- **SPEC_030 Stage G (standard witness):** Layer A, RawS1, Stage-C joint (**spelt out**, not `summitFE3_joint_semantic_law` in the type), APS **`ICompIdx`**, IC-native joint. -/
theorem standardRoleAwareRepresentationBundle :
    MasterStratifiedAdequacyCascadeAt icCS3HFinal.𝔠 icCS3HFinal.P icCS3HFinal.rcp ∧
      AbsoluteFrontierRawS1 icCorpusAlignedNonVacuousFinalAdequacy icCorpusAlignedBurden ∧
        (MasterStratifiedAdequacyCascadeAt certifiedFrontierRow_ic_cs3_aligned_nv.summitTagged.toHFinal.𝔠
              certifiedFrontierRow_ic_cs3_aligned_nv.summitTagged.toHFinal.P
              certifiedFrontierRow_ic_cs3_aligned_nv.summitTagged.toHFinal.rcp ∧
            ForgetfulIndexedCoherent certifiedFrontierRow_ic_cs3_aligned_nv.fe3.ops ∧
              ForgetfulAgreementInjects certifiedFrontierRow_ic_cs3_aligned_nv.fe3.ops) ∧
          (indexedApsRealizationLayer stdAPS).ICompIdx ∧
            ic_faithful_native_pair_cs3_nv_bridge_core_joint_prop :=
  And.intro ic_cs3_highest_reachable_summit_at
    (And.intro (absoluteFrontierRawS1_of_certifiedFrontierRow certifiedFrontierRow_ic_cs3_aligned_nv)
      (And.intro (certifiedFrontierRow_summitFE3_joint certifiedFrontierRow_ic_cs3_aligned_nv)
        (And.intro aps_stageE_std_summit_engine_yields_icomp
          ic_faithful_native_pair_cs3_nv_bridge_core_joint)))

end AdequacyArchitecture.Instances
