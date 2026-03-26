/-
  **SPEC_025 — Phase D:** **semantic reporting certificates** across the lawful summit / EPIC_018 outer
  boundary.

  The certificate **family** is indexed by a chosen outer `SemanticRemainder` witness, so Lean never
  elaborates a polymorphic `∧` mixing the lawful summit `Prop` layer with
  `faithfulNEMSHaltingReflexiveLayer.SemanticRemainder` in one **anonymous** conjunction.

  **Epistemic discipline:** no definitional identification of tracked grid content with outer remainder;
  the index only fixes **which** outer proof tabulates with **which** summit report.

  **Abstraction (NEMS vs general):** parameters use halting anchor and `faithfulNEMSHaltingReflexiveLayer`;
  other carriers need parallel indexed families.

  **Phase F:** **`halting_anchored_canonical_certificate_summit_agreement`** (`rfl` on indexed **`standard`**).
  **`NEMSHaltingSummitSemanticCertificate`** is the **witness-stripped** copy for **`HaltingAnchoredFaithfulSummitMasterBundle`**
  (option 1). Indexed **`NEMSHaltingAnchoredSemanticReportCertificate`** remains the Phase D interface; link
  via **`ofSummitCert`** / **`to_summit_only`**.
-/

import AdequacyArchitecture.Instances.NEMSFinalSummitLinkedReporting
import AdequacyArchitecture.Instances.NEMSFaithful

namespace AdequacyArchitecture.Instances

open AdequacyArchitecture.Lawful
open NemS.Framework
open NemS
open NemS.Physical

/-! ### Summit-only certificate (no EPIC_018 witness in the **family** index) — for master **`Type` bundles -/

/-- Same payload as **`NEMSHaltingAnchoredSemanticReportCertificate`**, but **not** indexed by outer
    `SemanticRemainder` — avoids stuck universe metavariables when packaging with lawful cascade + outer
    remainder in one **`structure`**. Re-index with **`to_indexed`** / Phase D family as needed. -/
structure NEMSHaltingSummitSemanticCertificate (h : HFinalFrameworkWithNEMAnchoredGlue)
    (hF : h.F₀ = haltingFramework) : Prop where
  summitTracked : HaltingAnchoredGluedSummitSemanticReport h hF

namespace NEMSHaltingSummitSemanticCertificate

variable {h : HFinalFrameworkWithNEMAnchoredGlue} {hF : h.F₀ = haltingFramework}

theorem ofReport (rep : HaltingAnchoredGluedSummitSemanticReport h hF) :
    NEMSHaltingSummitSemanticCertificate h hF :=
  ⟨rep⟩

theorem summitStandard (h : HFinalFrameworkWithNEMAnchoredGlue) (hF : h.F₀ = haltingFramework) :
    NEMSHaltingSummitSemanticCertificate h hF :=
  ⟨halting_anchored_glued_summit_semantic_report h hF⟩

theorem eq_of_summitTracked_eq {c₁ c₂ : NEMSHaltingSummitSemanticCertificate h hF}
    (ht : c₁.summitTracked = c₂.summitTracked) : c₁ = c₂ := by
  rcases c₁ with ⟨t₁⟩
  rcases c₂ with ⟨t₂⟩
  rcases ht
  rfl

end NEMSHaltingSummitSemanticCertificate

/-- Halting-anchored summit report **relative to** a chosen faithful outer `SemanticRemainder` witness. -/
structure NEMSHaltingAnchoredSemanticReportCertificate (h : HFinalFrameworkWithNEMAnchoredGlue)
    (hF : h.F₀ = haltingFramework)
    (outerWitness : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit) : Prop where
  summitTracked : HaltingAnchoredGluedSummitSemanticReport h hF

namespace NEMSHaltingAnchoredSemanticReportCertificate

variable {h : HFinalFrameworkWithNEMAnchoredGlue} {hF : h.F₀ = haltingFramework}
variable {outerWitness : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit}

/-- Tabulate a summit report under a fixed outer witness index. -/
theorem ofSummit (rep : HaltingAnchoredGluedSummitSemanticReport h hF) :
    NEMSHaltingAnchoredSemanticReportCertificate h hF outerWitness :=
  ⟨rep⟩

/-- **Canonical certificate:** index the standard unconditional outer proof. -/
theorem standard (h : HFinalFrameworkWithNEMAnchoredGlue) (hF : h.F₀ = haltingFramework) :
    NEMSHaltingAnchoredSemanticReportCertificate h hF faithful_nems_semantic_remainder_at_unit :=
  ⟨halting_anchored_glued_summit_semantic_report h hF⟩

/-- Repackage summit-only certificate at a chosen outer witness (phantom index / same `summitTracked`). -/
theorem ofSummitCert (w : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (c : NEMSHaltingSummitSemanticCertificate h hF) :
    NEMSHaltingAnchoredSemanticReportCertificate h hF w :=
  ⟨c.summitTracked⟩

/-- Canonical index. Defeq to **`ofSummitCert faithful_nems_semantic_remainder_at_unit c`**, but spelt with
    the constructor so elaboration does not leave stuck universe metavariables at that application. -/
theorem to_indexed_canonical_certificate (c : NEMSHaltingSummitSemanticCertificate h hF) :
    NEMSHaltingAnchoredSemanticReportCertificate h hF faithful_nems_semantic_remainder_at_unit :=
  ⟨c.summitTracked⟩

/-- One-field **`Prop`** certificate: equality from **`summitTracked`**. -/
theorem eq_of_summitTracked_eq {w}
    {c₁ c₂ : NEMSHaltingAnchoredSemanticReportCertificate h hF w}
    (ht : c₁.summitTracked = c₂.summitTracked) : c₁ = c₂ :=
  congrArg (fun r : HaltingAnchoredGluedSummitSemanticReport h hF =>
      (⟨r⟩ : NEMSHaltingAnchoredSemanticReportCertificate h hF w)) ht

theorem to_summit_only (c : NEMSHaltingAnchoredSemanticReportCertificate h hF outerWitness) :
    NEMSHaltingSummitSemanticCertificate h hF :=
  ⟨c.summitTracked⟩

theorem tracked_of (c : NEMSHaltingAnchoredSemanticReportCertificate h hF outerWitness) :
    @NemSemanticTrackedContent h.F₀ h.dc₀ :=
  c.summitTracked.tracked

theorem cascade_of (c : NEMSHaltingAnchoredSemanticReportCertificate h hF outerWitness) :
    MasterStratifiedAdequacyCascadeAt h.𝔠 h.P h.rcp :=
  c.summitTracked.cascade

/-- The outer fact is carried by the **index**; the certificate does not derive it from `summitTracked`. -/
theorem outer_from_index (w : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (_c : NEMSHaltingAnchoredSemanticReportCertificate h hF w) :
    faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit :=
  w

/-- For the **canonical** index, `outer_from_index` reads back that same proof term (defeq to
    `faithful_nems_semantic_remainder_at_unit` — cite `NEMSFaithful.lean`). -/
theorem outer_from_standard_certificate (h : HFinalFrameworkWithNEMAnchoredGlue) (hF : h.F₀ = haltingFramework)
    (c : NEMSHaltingAnchoredSemanticReportCertificate h hF faithful_nems_semantic_remainder_at_unit) :
    outer_from_index faithful_nems_semantic_remainder_at_unit c =
      faithful_nems_semantic_remainder_at_unit :=
  rfl

/-! ### Phase F — canonical agreement (`rfl` only) -/

/-- **Phase F (core):** **`standard`**’s `summitTracked` **is** **`halting_anchored_glued_summit_semantic_report`**. -/
theorem halting_anchored_canonical_certificate_summit_agreement
    (h : HFinalFrameworkWithNEMAnchoredGlue) (hF : h.F₀ = haltingFramework) :
    (standard h hF).summitTracked = halting_anchored_glued_summit_semantic_report h hF :=
  rfl

end NEMSHaltingAnchoredSemanticReportCertificate

end AdequacyArchitecture.Instances
