/-
  **SPEC_029_FR1 — FE-2 (NEMS):** theorem-fed faithful **`From*`** discharge routes through the **FE-3**
  **`IndexedPhantomCertificateOps`** / **`Core`** spine.

  **Artifact.** `NEMSFaithful.lean` — `concreteNEMSReflexiveLayer haltingFramework` /
  `faithful_nems_semantic_remainder_at_unit` (EPIC_018 remainder at `()`).

  **FE-3.** `NEMSBranchGenericSemanticTransport.lean` — `haltingAnchoredNemsIndexedPhantomOps`,
  `haltingAnchoredNemsBranchGenericCore`.

  **What is proved.** For `HaltingAnchoredFaithfulSummitMasterBundle`, FE-3 **`indexed`** and Phase **D**
  **`indexed_certificate faithful_nems_semantic_remainder_at_unit`** carry the same **`summitTracked`**;
  FE-3 **`summitReportOf`** agrees with that path and with **`agreed_summit`**. So corpus-facing discharge that
  tabulates at the **`From*`-proved** outer witness is **not** a parallel glue path: it is the same forgetful
  report field as the FE-3 interface (witness in the **certificate index** only).
-/

import AdequacyArchitecture.Instances.NEMSBranchGenericSemanticTransport
import AdequacyArchitecture.Instances.NEMSFaithful
import AdequacyArchitecture.Instances.NEMSSemanticFaithfulSummitMaster

namespace AdequacyArchitecture.Instances

open AdequacyArchitecture.Portability.BranchGenericSemanticTransport
open HaltingAnchoredFaithfulSummitMasterBundle
open NEMSHaltingAnchoredSemanticReportCertificate
open NemS.Framework
open NemS.MFRR
open NemS.Physical

variable {h : HFinalFrameworkWithNEMAnchoredGlue} {hF : h.F₀ = haltingFramework}

theorem nems_fe3_indexed_summitTracked_eq_indexed_certificate_at_faithful_from_star
    (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    ((@haltingAnchoredNemsIndexedPhantomOps h hF).indexed () b).summitTracked =
      (indexed_certificate faithful_nems_semantic_remainder_at_unit b).summitTracked :=
  rfl

theorem nems_fe3_summitReportOf_indexed_eq_indexed_certificate_faithful_summitTracked
    (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    @IndexedPhantomCertificateOps.summitReportOf _ _ _ _ (@haltingAnchoredNemsIndexedPhantomOps h hF) ()
        ((@haltingAnchoredNemsIndexedPhantomOps h hF).indexed () b) =
      (indexed_certificate faithful_nems_semantic_remainder_at_unit b).summitTracked :=
  rfl

theorem nems_fe3_agreed_summit_eq_indexed_certificate_faithful_summitTracked
    (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    agreed_summit b =
      (indexed_certificate faithful_nems_semantic_remainder_at_unit b).summitTracked :=
  rfl

theorem nems_fe3_ops_summitReportOf_indexed_eq_agreed_summit
    (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    @IndexedPhantomCertificateOps.summitReportOf _ _ _ _ (@haltingAnchoredNemsIndexedPhantomOps h hF) ()
        ((@haltingAnchoredNemsIndexedPhantomOps h hF).indexed () b) =
      agreed_summit b :=
  rfl

theorem nems_fe3_core_ops_eq_haltingAnchoredNemsIndexedPhantomOps :
    (haltingAnchoredNemsBranchGenericCore (h := h) (hF := hF)).ops =
      @haltingAnchoredNemsIndexedPhantomOps h hF :=
  rfl

/-  Certificate **equality** across the two outer witness spellings is intentionally **not** a single `Eq`:
    `indexed_certificate` families differ in the `outerWitness` index; **`summitTracked`** alignment is the
    discharge-relevant fact (**`nems_fe3_indexed_summitTracked_eq_indexed_certificate_at_faithful_from_star`**).
    Cite **`haltingAnchoredNems_indexed_eq_indexed_certificate`** for the FE-3 spelling vs `diagonal_barrier`. -/

end AdequacyArchitecture.Instances
