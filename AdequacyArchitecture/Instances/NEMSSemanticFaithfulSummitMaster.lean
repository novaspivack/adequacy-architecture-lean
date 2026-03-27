/-
  **SPEC_025 — Master bundle (option 1):** one **`Type`** witness for the halting faithful summit facts.

  Uses **`NEMSHaltingSummitSemanticCertificate`** (no outer witness in the certificate **type**) so the
  **`structure`** elaborates without universe metavariables. **EPIC_018** `SemanticRemainder` is **not** a
  field (same mismatch as **`HaltingAnchoredGluedSummitSemanticReport`**); compose **`faithful_nems_semantic_remainder_at_unit`**
  (`NEMSFaithful.lean`). For Phase D re-indexing use **`⟨c.summitTracked⟩`** / **`to_indexed_canonical_certificate`**
  (canonical) or **`ofSummitCert w`** (`NEMSSemanticReportCertificate.lean`) when **`w`** is a variable.

  **Do not** package core **`∧`₄** with the remainder in a single **`Prop`** **`∧`₂** next to **`b`**:
  elaboration hits a **`Prop` / `Type` sort mismatch** on `And` (nested summit `∧` indexed by a **`Type`** bundle).
  Cite **`as_fourfold_core b`** and **`faithful_nems_semantic_remainder_at_unit`** separately (see **`SPEC_025_YG2`**).

  **Option 2:** **`SPEC_025_YG2`** § *Official composition API*.

  **SPEC_032 HM4_K9N:** **`eq_mkStandard`** — at fixed **`(h, hF)`**, **only one** summit master bundle up to equality (**`mkStandard`**); see **`SPEC_032_HM4_K9N_NEMS_MASTER_BUNDLE_SUBSINGLETON_SPINE.md`**.
-/

import AdequacyArchitecture.Instances.NEMSFinalSummitSemanticGlue
import AdequacyArchitecture.Instances.NEMSSemanticReportCertificate

namespace AdequacyArchitecture.Instances

open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open NEMSHaltingAnchoredSemanticReportCertificate
open NemS.Framework
open NemS
open NemS.Physical

structure HaltingAnchoredFaithfulSummitMasterBundle (h : HFinalFrameworkWithNEMAnchoredGlue)
    (hF : h.F₀ = haltingFramework) : Type where
  lawfulCascade : MasterStratifiedAdequacyCascadeAt h.𝔠 h.P h.rcp
  summitCert : NEMSHaltingSummitSemanticCertificate h hF
  truthWitness : ExistentialTruthWitness h.F₀
  summit_agrees : summitCert.summitTracked = halting_anchored_glued_summit_semantic_report h hF

namespace HaltingAnchoredFaithfulSummitMasterBundle

variable {h : HFinalFrameworkWithNEMAnchoredGlue} {hF : h.F₀ = haltingFramework}

def mkStandard (h : HFinalFrameworkWithNEMAnchoredGlue) (hF : h.F₀ = haltingFramework) :
    HaltingAnchoredFaithfulSummitMasterBundle h hF where
  lawfulCascade := highestReachable_summit_at h.toHFinal
  summitCert := NEMSHaltingSummitSemanticCertificate.summitStandard h hF
  truthWitness := existential_truth_witness_of_aligned_summit h
  summit_agrees := rfl

def agreed_summit (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    HaltingAnchoredGluedSummitSemanticReport h hF :=
  b.summitCert.summitTracked

/-- Phase D indexed certificate at the **canonical** outer witness, recovered from the bundle. -/
def indexed_canonical_certificate (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    NEMSHaltingAnchoredSemanticReportCertificate h hF faithful_nems_semantic_remainder_at_unit :=
  ⟨b.summitCert.summitTracked⟩

/-- Indexed certificate at an **arbitrary** outer tabulation tag (same `summitTracked`). -/
def indexed_certificate (w : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    NEMSHaltingAnchoredSemanticReportCertificate h hF w :=
  ⟨b.summitCert.summitTracked⟩

/-- **Canonical** packaging is **defeq** to **`indexed_certificate`** at **`faithful_nems_semantic_remainder_at_unit`**. -/
theorem indexed_certificate_faithful_nems_eq_indexed_canonical
    (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    indexed_certificate faithful_nems_semantic_remainder_at_unit b = indexed_canonical_certificate b :=
  rfl

theorem indexed_canonical_eq_standard (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    indexed_canonical_certificate b = NEMSHaltingAnchoredSemanticReportCertificate.standard h hF := by
  rcases b with ⟨_, _, _, hag⟩
  exact NEMSHaltingAnchoredSemanticReportCertificate.eq_of_summitTracked_eq hag

/-- **`∧`₄** from the bundle (lawful + summit cert + existential Truth + summit agreement). -/
theorem as_fourfold_core (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    MasterStratifiedAdequacyCascadeAt h.𝔠 h.P h.rcp ∧
      NEMSHaltingSummitSemanticCertificate h hF ∧
      ExistentialTruthWitness h.F₀ ∧
      b.summitCert.summitTracked = halting_anchored_glued_summit_semantic_report h hF :=
  ⟨b.lawfulCascade, b.summitCert, b.truthWitness, b.summit_agrees⟩

/-! ### Projections from **`as_fourfold_core`** (citation ergonomics; `∧` associates right) -/

theorem as_fourfold_core_lawfulCascade (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    (as_fourfold_core b).1 = b.lawfulCascade :=
  rfl

theorem as_fourfold_core_summitCert (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    (as_fourfold_core b).2.1 = b.summitCert :=
  rfl

theorem as_fourfold_core_truthWitness (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    (as_fourfold_core b).2.2.1 = b.truthWitness :=
  rfl

theorem as_fourfold_core_summit_agrees (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    (as_fourfold_core b).2.2.2 = b.summit_agrees :=
  rfl

theorem mkStandard_lawfulCascade :
    (mkStandard h hF).lawfulCascade = highestReachable_summit_at h.toHFinal :=
  rfl

theorem mkStandard_summitCert :
    (mkStandard h hF).summitCert = NEMSHaltingSummitSemanticCertificate.summitStandard h hF :=
  rfl

theorem mkStandard_truthWitness :
    (mkStandard h hF).truthWitness = existential_truth_witness_of_aligned_summit h :=
  rfl

theorem to_indexed_canonical_certificate_eq_indexed_canonical
    (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    to_indexed_canonical_certificate b.summitCert = indexed_canonical_certificate b :=
  rfl

/--
  **SPEC_032 (HM4 prerequisite):** **`summit_agrees`** forces **`summitCert`** to **`summitStandard`**.
-/
theorem summitCert_eq_summitStandard (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    b.summitCert = NEMSHaltingSummitSemanticCertificate.summitStandard h hF :=
  NEMSHaltingSummitSemanticCertificate.eq_of_summitTracked_eq b.summit_agrees

/--
  At fixed **`(h, hF)`**, **every** halting-anchored faithful summit master bundle equals **`mkStandard h hF`**:
  **`summit_agrees`** pins **`summitCert`** to **`summitStandard`**, and the remaining **`Prop`** fields agree with
  **`mkStandard`** by proof irrelevance after **`subst`**. Hence **no** genuinely **distinct** pairs in
  **`HaltingAnchoredFaithfulSummitMasterBundle h hF`** — see **`SPEC_032_HM4_K9N`**.
-/
theorem eq_mkStandard (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    b = mkStandard h hF := by
  rcases b with ⟨lc, sc, tw, sa⟩
  have hsc : sc = NEMSHaltingSummitSemanticCertificate.summitStandard h hF :=
    NEMSHaltingSummitSemanticCertificate.eq_of_summitTracked_eq sa
  subst hsc
  dsimp only [mkStandard]

/--
  **Corollary:** any **`γ`-indexed** family of master bundles is **extensionally** the **constant** **`mkStandard`** map.
-/
theorem eqFun_const_mkStandard {γ : Type} (b : γ → HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    b = fun _ => mkStandard h hF :=
  funext fun x => eq_mkStandard (b x)

end HaltingAnchoredFaithfulSummitMasterBundle

abbrev halting_anchored_faithful_summit_master_bundle
    (h : HFinalFrameworkWithNEMAnchoredGlue) (hF : h.F₀ = haltingFramework) :
    HaltingAnchoredFaithfulSummitMasterBundle h hF :=
  HaltingAnchoredFaithfulSummitMasterBundle.mkStandard h hF

theorem mkStandard_eq_halting_anchored_faithful_summit_master_bundle
    (h : HFinalFrameworkWithNEMAnchoredGlue) (hF : h.F₀ = haltingFramework) :
    HaltingAnchoredFaithfulSummitMasterBundle.mkStandard h hF =
      halting_anchored_faithful_summit_master_bundle h hF :=
  rfl

end AdequacyArchitecture.Instances
