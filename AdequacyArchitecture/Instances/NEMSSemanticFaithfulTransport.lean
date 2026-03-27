/-
  **SPEC_025 — Faithful semantic transport:** how **`HaltingAnchoredFaithfulSummitMasterBundle`**
  (summit **`Type`** package) relates to Phase **C–E** report / certificate / forgetful–reindex morphisms.

  **Purpose.** Turn the master bundle + normative API into an explicit **transport interface**: projections
  to **`HaltingAnchoredGluedSummitSemanticReport`**, indexed certificates at any outer tag, invariance of
  report content under **`reindex` / `reindex_arbitrary`**, alignment with the authoritative
  **`halting_anchored_glued_summit_semantic_report`** via **`summit_agrees`**, and **recovery** of the
  companion outer fact **only through the certificate index** (`outer_from_index`), never from
  **`summitTracked`** alone.

  **Epistemic discipline (unchanged).** Do **not** add **`SemanticRemainder`** to the master bundle; cite
  **`faithful_nems_semantic_remainder_at_unit`** as a sibling (see **`SPEC_025_YG2`** § *Official composition
  API*). **`MasterBundleCascadeCoherent`** is an optional hypothesis tying **`lawfulCascade`** to the
  **`summitTracked`** cascade (alternative citation paths); **every** valid bundle is **`mkStandard`**-equal anyway
  (**`HaltingAnchoredFaithfulSummitMasterBundle.eq_mkStandard`** — **`SPEC_032_HM4_K9N`**).

  **Depends on:** **`NEMSSemanticFaithfulSummitMaster`**, **`NEMSSemanticReportCertificateTransport`**
  (Phase E). For certificate primitives see **`NEMSSemanticReportCertificate`**.

  **`summitReportOf` / master bundle:** equality of forgetful images at **any** phantom tags
  (**`agreed_summit_eq_of_summitReportOf_indexed_eq`**) lifts to **`agreed_summit`**, **`summitCert`**, and
  **indexed certificates at a chosen `w₀`**; the last uses **`congrArg`** on **`⟨·⟩`** (avoids stuck universe
  metas from chaining **`eq_of_summitTracked_eq`** with polymorphic **`summitReportOf_indexed`** applications).
-/

import AdequacyArchitecture.Instances.NEMSSemanticFaithfulSummitMaster
import AdequacyArchitecture.Instances.NEMSSemanticReportCertificateTransport

namespace AdequacyArchitecture.Instances

namespace NEMSSemanticFaithfulTransport

open AdequacyArchitecture.Lawful
open ReflexiveArchitecture.Instances
open HaltingAnchoredFaithfulSummitMasterBundle
open NEMSHaltingAnchoredSemanticReportCertificate
open NEMSHaltingSummitSemanticCertificate
open NemS.Framework
open NemS
open NemS.Physical

variable {h : HFinalFrameworkWithNEMAnchoredGlue} {hF : h.F₀ = haltingFramework}
variable {w w₁ w₂ w₃ : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit}

/-! ## Master bundle → summit report (Phase C) via forgetful map -/

theorem summitReportOf_indexed_canonical (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    summitReportOf (indexed_canonical_certificate b) = agreed_summit b :=
  rfl

theorem summitReportOf_indexed (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    summitReportOf (indexed_certificate w b) = agreed_summit b :=
  rfl

theorem agreed_summit_eq_halting_report (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    agreed_summit b = halting_anchored_glued_summit_semantic_report h hF :=
  b.summit_agrees

theorem summitReportOf_indexed_canonical_eq_authoritative (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    summitReportOf (indexed_canonical_certificate b) = halting_anchored_glued_summit_semantic_report h hF :=
  b.summit_agrees

theorem summitReportOf_indexed_eq_authoritative (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    summitReportOf (indexed_certificate w b) = halting_anchored_glued_summit_semantic_report h hF :=
  b.summit_agrees

/-! ## Master bundle ↔ Phase D (summit-only ↔ indexed) -/

theorem indexed_certificate_eq_ofSummitCert (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    indexed_certificate w b = ofSummitCert w b.summitCert :=
  rfl

theorem to_summit_only_indexed_canonical (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    to_summit_only (indexed_canonical_certificate b) = b.summitCert :=
  rfl

theorem to_summit_only_indexed (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    to_summit_only (indexed_certificate w b) = b.summitCert :=
  rfl

theorem indexed_canonical_eq_to_indexed (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    indexed_canonical_certificate b = to_indexed_canonical_certificate b.summitCert :=
  rfl

/-! ## Indexed certificates as **`ofSummit (agreed_summit b)`** (same `summitTracked`) -/

theorem indexed_certificate_eq_ofSummit_agreed (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    indexed_certificate w b = @ofSummit h hF w (agreed_summit b) :=
  rfl

theorem indexed_canonical_certificate_eq_ofSummit_agreed (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    indexed_canonical_certificate b =
      @ofSummit h hF faithful_nems_semantic_remainder_at_unit (agreed_summit b) :=
  rfl

theorem summitReportOf_ofSummit_agreed (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    summitReportOf (@ofSummit h hF w (agreed_summit b)) = agreed_summit b :=
  rfl

theorem to_summit_only_ofSummit_agreed (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    to_summit_only (@ofSummit h hF w (agreed_summit b)) = b.summitCert :=
  rfl

theorem cascade_of_indexed_eq_cascade_of_agreed (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    cascade_of (indexed_certificate w b) = (agreed_summit b).cascade :=
  rfl

theorem cascade_of_indexed_canonical_eq_cascade_of_agreed (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    cascade_of (indexed_canonical_certificate b) = (agreed_summit b).cascade :=
  rfl

theorem tracked_of_indexed_eq_tracked_of_agreed (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    tracked_of (indexed_certificate w b) = (agreed_summit b).tracked :=
  rfl

theorem tracked_of_indexed_canonical_eq_tracked_of_agreed (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    tracked_of (indexed_canonical_certificate b) = (agreed_summit b).tracked :=
  rfl

/-- **`as_fourfold_core` · summit certificate** is **`to_summit_only`** of any master-indexed witness. -/
theorem as_fourfold_summitCert_eq_to_summit_only_indexed (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    (as_fourfold_core b).2.1 = to_summit_only (indexed_certificate w b) :=
  rfl

theorem as_fourfold_summitCert_eq_to_summit_only_indexed_canonical
    (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    (as_fourfold_core b).2.1 = to_summit_only (indexed_canonical_certificate b) :=
  rfl

/-! ## Reindexing (phantom outer tag) — summit-only certificate layer first -/

/-- Phase **E** reindex along `w₁ = w₂` for certificates built from **`ofSummitCert`** (no **`Type`** bundle). -/
theorem reindex_ofSummitCert_eq (e : w₁ = w₂) (sc : NEMSHaltingSummitSemanticCertificate h hF) :
    reindex e (ofSummitCert w₁ sc) = ofSummitCert w₂ sc :=
  eq_of_summitTracked_eq rfl

/-! ## Reindexing invariance (phantom outer tag) — master bundle via `b.summitCert` -/

theorem master_indexed_reindex_arbitrary (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    reindex_arbitrary w₂ (indexed_certificate w₁ b) = indexed_certificate w₂ b :=
  rfl

theorem master_indexed_reindex (e : w₁ = w₂) (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    reindex e (indexed_certificate w₁ b) = indexed_certificate w₂ b :=
  rfl

/-- Path-composition functoriality for master-indexed certificates. -/
theorem master_indexed_reindex_trans (e₁₂ : w₁ = w₂) (e₂₃ : w₂ = w₃)
    (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    reindex (e₁₂.trans e₂₃) (indexed_certificate w₁ b) =
      reindex e₂₃ (reindex e₁₂ (indexed_certificate w₁ b)) :=
  rfl

theorem master_indexed_reindex_eq_reindex_arbitrary (e : w₁ = w₂)
    (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    reindex e (indexed_certificate w₁ b) = reindex_arbitrary w₂ (indexed_certificate w₁ b) :=
  rfl

theorem master_reindex_reindex_symm (e : w₁ = w₂) (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    reindex e.symm (reindex e (indexed_certificate w₁ b)) = indexed_certificate w₁ b :=
  rfl

theorem master_reindex_symm_reindex (e : w₁ = w₂) (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    reindex e (reindex e.symm (indexed_certificate w₂ b)) = indexed_certificate w₂ b :=
  rfl

theorem master_reindex_arbitrary_self (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    reindex_arbitrary w (indexed_certificate w b) = indexed_certificate w b :=
  rfl

theorem summitReportOf_reindex_master (e : w₁ = w₂) (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    summitReportOf (reindex e (indexed_certificate w₁ b)) = agreed_summit b :=
  rfl

theorem summitReportOf_reindex_arbitrary_master (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    summitReportOf (reindex_arbitrary w₂ (indexed_certificate w₁ b)) = agreed_summit b :=
  rfl

theorem ofSummit_summitReportOf_indexed (b : HaltingAnchoredFaithfulSummitMasterBundle h hF)
    (w₀ : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit) :
    ofSummit (summitReportOf (indexed_certificate w₀ b)) = indexed_certificate w₀ b :=
  rfl

/-! ## Outer tabulation tag (**`outerWitnessOf`**) — master-indexed certificates -/

theorem outerWitnessOf_indexed_certificate (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    outerWitnessOf (indexed_certificate w b) = w :=
  rfl

theorem outerWitnessOf_indexed_canonical_certificate (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    outerWitnessOf (indexed_canonical_certificate b) = faithful_nems_semantic_remainder_at_unit :=
  rfl

theorem outerWitnessOf_reindex_master_indexed (e : w₁ = w₂) (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    outerWitnessOf (reindex e (indexed_certificate w₁ b)) = w₂ :=
  rfl

theorem outerWitnessOf_reindex_arbitrary_master (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    outerWitnessOf (reindex_arbitrary w₂ (indexed_certificate w₁ b)) = w₂ :=
  rfl

/-! ## Phase E reindex commutes with **`tracked_of`** / **`cascade_of`** — master bundle -/

theorem tracked_of_master_indexed_reindex (e : w₁ = w₂) (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    tracked_of (reindex e (indexed_certificate w₁ b)) = tracked_of (indexed_certificate w₁ b) :=
  rfl

theorem cascade_of_master_indexed_reindex (e : w₁ = w₂) (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    cascade_of (reindex e (indexed_certificate w₁ b)) = cascade_of (indexed_certificate w₁ b) :=
  rfl

theorem tracked_of_master_indexed_reindex_arbitrary (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    tracked_of (reindex_arbitrary w₂ (indexed_certificate w₁ b)) =
      tracked_of (indexed_certificate w₁ b) :=
  rfl

theorem cascade_of_master_indexed_reindex_arbitrary (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    cascade_of (reindex_arbitrary w₂ (indexed_certificate w₁ b)) =
      cascade_of (indexed_certificate w₁ b) :=
  rfl

theorem to_summit_only_master_indexed_reindex (e : w₁ = w₂)
    (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    to_summit_only (reindex e (indexed_certificate w₁ b)) = b.summitCert :=
  rfl

theorem to_summit_only_master_indexed_reindex_arbitrary (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    to_summit_only (reindex_arbitrary w₂ (indexed_certificate w₁ b)) = b.summitCert :=
  rfl

/-- Equal **reindexed** master certificates ⇒ equal **`summitCert`**. -/
theorem summitCert_eq_of_master_indexed_reindex_eq (e : w₁ = w₂)
    {b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF}
    (hr : reindex e (indexed_certificate w₁ b₁) = reindex e (indexed_certificate w₁ b₂)) :
    b₁.summitCert = b₂.summitCert := by
  rcases b₁ with ⟨_, sc₁, _, _⟩
  rcases b₂ with ⟨_, sc₂, _, _⟩
  rcases sc₁ with ⟨_⟩
  rcases sc₂ with ⟨_⟩
  rcases hr
  rfl

theorem summitCert_eq_of_master_reindex_arbitrary_eq
    {b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF}
    (hr : reindex_arbitrary w₂ (indexed_certificate w₁ b₁) =
      reindex_arbitrary w₂ (indexed_certificate w₁ b₂)) :
    b₁.summitCert = b₂.summitCert := by
  rcases b₁ with ⟨_, sc₁, _, _⟩
  rcases b₂ with ⟨_, sc₂, _, _⟩
  rcases sc₁ with ⟨_⟩
  rcases sc₂ with ⟨_⟩
  rcases hr
  rfl

theorem agreed_summit_eq_of_master_indexed_reindex_eq (e : w₁ = w₂)
    {b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF}
    (hr : reindex e (indexed_certificate w₁ b₁) = reindex e (indexed_certificate w₁ b₂)) :
    agreed_summit b₁ = agreed_summit b₂ :=
  congrArg NEMSHaltingAnchoredSemanticReportCertificate.summitTracked hr

theorem agreed_summit_eq_of_master_reindex_arbitrary_eq
    {b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF}
    (hr : reindex_arbitrary w₂ (indexed_certificate w₁ b₁) =
      reindex_arbitrary w₂ (indexed_certificate w₁ b₂)) :
    agreed_summit b₁ = agreed_summit b₂ :=
  congrArg NEMSHaltingAnchoredSemanticReportCertificate.summitTracked hr

/-- Phase **G** counterpart to Phase **E** **`ofSummit_summitReportOf_reindex_arbitrary`**. **`rfl`**
    (both sides **`⟨agreed_summit b⟩`** at `w₀`); avoids term-mode **`congrArg @ofSummit`** universe artifacts. -/
theorem ofSummit_summitReportOf_reindex_arbitrary_master
    (w₀ : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    @ofSummit h hF w₀ (summitReportOf (reindex_arbitrary w₀ (indexed_certificate w₁ b))) =
      reindex_arbitrary w₀ (indexed_certificate w₁ b) :=
  rfl

/-- Same **definitional** section law for **`reindex`** along a path (**`w₂`** destination tag). -/
theorem ofSummit_summitReportOf_reindex_master (e : w₁ = w₂)
    (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    @ofSummit h hF w₂ (summitReportOf (reindex e (indexed_certificate w₁ b))) =
      reindex e (indexed_certificate w₁ b) :=
  rfl

/-- **`agreed_summit`** determines **`summitCert`** (converse direction to **`agreed_summit_eq_of_bundle_summitCert_eq`**). -/
theorem summitCert_eq_of_agreed_summit_eq
    {b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF}
    (hag : agreed_summit b₁ = agreed_summit b₂) :
    b₁.summitCert = b₂.summitCert :=
  NEMSHaltingSummitSemanticCertificate.eq_of_summitTracked_eq hag

/-- Fixed outer tag: equal indexed certificates ⇒ equal **`agreed_summit`** / summit report payload. -/
theorem agreed_summit_eq_of_indexed_certificate_eq
    {b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF}
    (w₀ : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (hi : indexed_certificate w₀ b₁ = indexed_certificate w₀ b₂) :
    agreed_summit b₁ = agreed_summit b₂ :=
  congrArg NEMSHaltingAnchoredSemanticReportCertificate.summitTracked hi

theorem indexed_certificate_eq_of_agreed_summit_eq
    {b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF}
    (hag : agreed_summit b₁ = agreed_summit b₂)
    (w₀ : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit) :
    indexed_certificate w₀ b₁ = indexed_certificate w₀ b₂ :=
  eq_of_summitTracked_eq hag

theorem indexed_canonical_certificate_eq_of_agreed_summit_eq
    {b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF}
    (hag : agreed_summit b₁ = agreed_summit b₂) :
    indexed_canonical_certificate b₁ = indexed_canonical_certificate b₂ :=
  eq_of_summitTracked_eq hag

/-- **`summitReportOf`** on master-indexed certs ignores the phantom tag — equality of those images is
    **`agreed_summit`** agreement (any pair of index choices). -/
theorem agreed_summit_eq_of_summitReportOf_indexed_eq
    {b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF}
    (w_a w_b : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (hsr : summitReportOf (indexed_certificate w_a b₁) = summitReportOf (indexed_certificate w_b b₂)) :
    agreed_summit b₁ = agreed_summit b₂ :=
  hsr

theorem summitCert_eq_of_summitReportOf_indexed_eq
    {b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF}
    (w_a w_b : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (hsr : summitReportOf (indexed_certificate w_a b₁) = summitReportOf (indexed_certificate w_b b₂)) :
    b₁.summitCert = b₂.summitCert :=
  summitCert_eq_of_agreed_summit_eq (b₁ := b₁) (b₂ := b₂) hsr

theorem indexed_certificate_eq_of_summitReportOf_indexed_eq
    {b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF}
    (w_a w_b : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (hsr : summitReportOf (indexed_certificate w_a b₁) = summitReportOf (indexed_certificate w_b b₂))
    (w₀ : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit) :
    indexed_certificate w₀ b₁ = indexed_certificate w₀ b₂ :=
  congrArg (fun r : HaltingAnchoredGluedSummitSemanticReport h hF =>
      (⟨r⟩ : NEMSHaltingAnchoredSemanticReportCertificate h hF w₀)) hsr

/-- Same entailment as **`indexed_certificate_eq_of_summitReportOf_indexed_eq`**, at the **canonical** index. -/
theorem indexed_canonical_certificate_eq_of_summitReportOf_indexed_eq
    {b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF}
    (w_a w_b : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (hsr : summitReportOf (indexed_certificate w_a b₁) = summitReportOf (indexed_certificate w_b b₂)) :
    indexed_canonical_certificate b₁ = indexed_canonical_certificate b₂ :=
  eq_of_summitTracked_eq hsr

theorem indexed_canonical_certificate_eq_of_summitReportOf_indexed_canonical_eq
    {b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF}
    (hsr : summitReportOf (indexed_canonical_certificate b₁) = summitReportOf (indexed_canonical_certificate b₂)) :
    indexed_canonical_certificate b₁ = indexed_canonical_certificate b₂ :=
  eq_of_summitTracked_eq hsr

theorem indexed_certificate_eq_of_summitReportOf_indexed_canonical_indexed_eq
    {b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF}
    (w_b : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (hsr : summitReportOf (indexed_canonical_certificate b₁) = summitReportOf (indexed_certificate w_b b₂))
    (w₀ : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit) :
    indexed_certificate w₀ b₁ = indexed_certificate w₀ b₂ :=
  congrArg (fun r : HaltingAnchoredGluedSummitSemanticReport h hF =>
      (⟨r⟩ : NEMSHaltingAnchoredSemanticReportCertificate h hF w₀)) hsr

theorem indexed_certificate_eq_of_summitReportOf_indexed_indexed_canonical_eq
    {b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF}
    (w_a : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (hsr : summitReportOf (indexed_certificate w_a b₁) = summitReportOf (indexed_canonical_certificate b₂))
    (w₀ : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit) :
    indexed_certificate w₀ b₁ = indexed_certificate w₀ b₂ :=
  congrArg (fun r : HaltingAnchoredGluedSummitSemanticReport h hF =>
      (⟨r⟩ : NEMSHaltingAnchoredSemanticReportCertificate h hF w₀)) hsr

theorem summitCert_eq_of_summitReportOf_indexed_canonical_indexed_eq
    {b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF}
    (w_b : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (hsr : summitReportOf (indexed_canonical_certificate b₁) = summitReportOf (indexed_certificate w_b b₂)) :
    b₁.summitCert = b₂.summitCert :=
  summitCert_eq_of_agreed_summit_eq (b₁ := b₁) (b₂ := b₂) hsr

theorem summitCert_eq_of_summitReportOf_indexed_indexed_canonical_eq
    {b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF}
    (w_a : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (hsr : summitReportOf (indexed_certificate w_a b₁) = summitReportOf (indexed_canonical_certificate b₂)) :
    b₁.summitCert = b₂.summitCert :=
  summitCert_eq_of_agreed_summit_eq (b₁ := b₁) (b₂ := b₂) hsr

/-! ## Higher summit — forgetful agreement through fourfold + Phase D relabelling (`SPEC_025`)

  These lemmas lift **`summitReportOf`-equality** on master-indexed witnesses to the **summit-certificate
  slot** of **`as_fourfold_core`**, to **canonical indexed Phase D** certificates, **arbitrary `ofSummitCert`**
  re-tabulation, **grid** projections of **`agreed_summit`**, and **`to_summit_only`** (**proof** is
  **`summitCert_eq_of_agreed_summit_eq`** — goal **defeq** to **`b₁.summitCert = b₂.summitCert`** via
  **`to_summit_only_indexed`**). Still **no** full bundle extensionality: **`lawfulCascade`** /
  **`truthWitness`** are not determined by the forgetful image. -/

theorem as_fourfold_summitCert_eq_of_summitReportOf_indexed_eq
    {b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF}
    (w_a w_b : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (hsr : summitReportOf (indexed_certificate w_a b₁) = summitReportOf (indexed_certificate w_b b₂)) :
    (as_fourfold_core b₁).2.1 = (as_fourfold_core b₂).2.1 :=
  (as_fourfold_core_summitCert b₁).trans
    ((summitCert_eq_of_agreed_summit_eq (b₁ := b₁) (b₂ := b₂) hsr).trans (as_fourfold_core_summitCert b₂).symm)

theorem to_indexed_canonical_certificate_eq_of_summitReportOf_indexed_eq
    {b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF}
    (w_a w_b : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (hsr : summitReportOf (indexed_certificate w_a b₁) = summitReportOf (indexed_certificate w_b b₂)) :
    to_indexed_canonical_certificate b₁.summitCert = to_indexed_canonical_certificate b₂.summitCert := by
  rw [summitCert_eq_of_agreed_summit_eq (b₁ := b₁) (b₂ := b₂) hsr]

theorem ofSummitCert_eq_of_summitReportOf_indexed_eq
    {b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF}
    (w_a w_b w₀ : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (hsr : summitReportOf (indexed_certificate w_a b₁) = summitReportOf (indexed_certificate w_b b₂)) :
    ofSummitCert w₀ b₁.summitCert = ofSummitCert w₀ b₂.summitCert := by
  rw [summitCert_eq_of_agreed_summit_eq (b₁ := b₁) (b₂ := b₂) hsr]

theorem agreed_summit_cascade_eq_of_summitReportOf_indexed_eq
    {b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF}
    (w_a w_b : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (hsr : summitReportOf (indexed_certificate w_a b₁) = summitReportOf (indexed_certificate w_b b₂)) :
    (agreed_summit b₁).cascade = (agreed_summit b₂).cascade :=
  congrArg HaltingAnchoredGluedSummitSemanticReport.cascade hsr

theorem agreed_summit_tracked_eq_of_summitReportOf_indexed_eq
    {b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF}
    (w_a w_b : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (hsr : summitReportOf (indexed_certificate w_a b₁) = summitReportOf (indexed_certificate w_b b₂)) :
    (agreed_summit b₁).tracked = (agreed_summit b₂).tracked :=
  congrArg HaltingAnchoredGluedSummitSemanticReport.tracked hsr

theorem to_summit_only_indexed_eq_of_summitReportOf_indexed_eq
    {b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF}
    (w_a w_b : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (hsr : summitReportOf (indexed_certificate w_a b₁) = summitReportOf (indexed_certificate w_b b₂))
    (w₀ : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit) :
    to_summit_only (indexed_certificate w₀ b₁) = to_summit_only (indexed_certificate w₀ b₂) :=
  summitCert_eq_of_agreed_summit_eq (b₁ := b₁) (b₂ := b₂) hsr

theorem cascade_of_indexed_eq_of_summitReportOf_indexed_eq
    {b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF}
    (w_a w_b : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (hsr : summitReportOf (indexed_certificate w_a b₁) = summitReportOf (indexed_certificate w_b b₂))
    (w₀ : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit) :
    cascade_of (indexed_certificate w₀ b₁) = cascade_of (indexed_certificate w₀ b₂) :=
  congrArg HaltingAnchoredGluedSummitSemanticReport.cascade hsr

theorem tracked_of_indexed_eq_of_summitReportOf_indexed_eq
    {b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF}
    (w_a w_b : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (hsr : summitReportOf (indexed_certificate w_a b₁) = summitReportOf (indexed_certificate w_b b₂))
    (w₀ : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit) :
    tracked_of (indexed_certificate w₀ b₁) = tracked_of (indexed_certificate w₀ b₂) :=
  congrArg HaltingAnchoredGluedSummitSemanticReport.tracked hsr

theorem ofSummit_agreed_eq_of_summitReportOf_indexed_eq
    {b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF}
    (w_a w_b : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (hsr : summitReportOf (indexed_certificate w_a b₁) = summitReportOf (indexed_certificate w_b b₂))
    (w₀ : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit) :
    @ofSummit h hF w₀ (agreed_summit b₁) = @ofSummit h hF w₀ (agreed_summit b₂) :=
  congrArg (fun r : HaltingAnchoredGluedSummitSemanticReport h hF =>
      (⟨r⟩ : NEMSHaltingAnchoredSemanticReportCertificate h hF w₀)) hsr

/-!
## Maximal SPEC_025 master-bundle packaging (within the forgetful image)

  Single `And` block listing **all** lifted equalities from **`summitReportOf`-agreement** on
  master-indexed certificates (still **no** **`lawfulCascade`/`truthWitness`** extensionality from **`hsr`**
  alone — cite **`MasterBundleCascadeCoherent`** for Layer-A alignment when needed).

  Program **apex** (raw S1/S2 over arbitrary `P`,`B`, representation, corpus-native bridges) remains outside
  this layer — see **`STATUS_AND_HANDOFF`** / **`SPEC_015`**. -/

theorem summitReportOf_indexed_master_agreement_consequences
    {h : HFinalFrameworkWithNEMAnchoredGlue} {hF : h.F₀ = haltingFramework}
    {b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF}
    (w_a w_b : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (hsr : summitReportOf (indexed_certificate w_a b₁) = summitReportOf (indexed_certificate w_b b₂)) :
    agreed_summit b₁ = agreed_summit b₂ ∧
    b₁.summitCert = b₂.summitCert ∧
    (∀ w₀ : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit,
        indexed_certificate w₀ b₁ = indexed_certificate w₀ b₂) ∧
    indexed_canonical_certificate b₁ = indexed_canonical_certificate b₂ ∧
    (as_fourfold_core b₁).2.1 = (as_fourfold_core b₂).2.1 ∧
    to_indexed_canonical_certificate b₁.summitCert = to_indexed_canonical_certificate b₂.summitCert ∧
    (∀ w₀ : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit,
        ofSummitCert w₀ b₁.summitCert = ofSummitCert w₀ b₂.summitCert) ∧
    (agreed_summit b₁).cascade = (agreed_summit b₂).cascade ∧
    (agreed_summit b₁).tracked = (agreed_summit b₂).tracked ∧
    (∀ w₀ : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit,
        to_summit_only (indexed_certificate w₀ b₁) = to_summit_only (indexed_certificate w₀ b₂)) ∧
    (∀ w₀ : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit,
        cascade_of (indexed_certificate w₀ b₁) = cascade_of (indexed_certificate w₀ b₂)) ∧
    (∀ w₀ : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit,
        tracked_of (indexed_certificate w₀ b₁) = tracked_of (indexed_certificate w₀ b₂)) ∧
    (∀ w₀ : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit,
        @ofSummit h hF w₀ (agreed_summit b₁) = @ofSummit h hF w₀ (agreed_summit b₂)) := by
  /- Do not compose the packaged lemma names here: reusing those theorem constants in one huge `∧` type
    leaves their shared dependent universes unresolved (Lean reports stuck `?u` on each apply). -/
  refine And.intro hsr ?_
  refine And.intro (summitCert_eq_of_agreed_summit_eq (b₁ := b₁) (b₂ := b₂) hsr) ?_
  refine And.intro (fun w₀ =>
      congrArg (fun r : HaltingAnchoredGluedSummitSemanticReport h hF =>
            (⟨r⟩ : NEMSHaltingAnchoredSemanticReportCertificate h hF w₀))
        hsr) ?_
  refine And.intro (eq_of_summitTracked_eq hsr) ?_
  refine And.intro
      ((as_fourfold_core_summitCert b₁).trans
        ((summitCert_eq_of_agreed_summit_eq (b₁ := b₁) (b₂ := b₂) hsr).trans (as_fourfold_core_summitCert b₂).symm))
    ?_
  refine And.intro (by rw [summitCert_eq_of_agreed_summit_eq (b₁ := b₁) (b₂ := b₂) hsr]) ?_
  refine And.intro (fun w₀ => by rw [summitCert_eq_of_agreed_summit_eq (b₁ := b₁) (b₂ := b₂) hsr]) ?_
  refine And.intro (congrArg HaltingAnchoredGluedSummitSemanticReport.cascade hsr) ?_
  refine And.intro (congrArg HaltingAnchoredGluedSummitSemanticReport.tracked hsr) ?_
  refine And.intro (fun _w₀ => summitCert_eq_of_agreed_summit_eq (b₁ := b₁) (b₂ := b₂) hsr) ?_
  refine And.intro (fun _w₀ => congrArg HaltingAnchoredGluedSummitSemanticReport.cascade hsr) ?_
  refine And.intro (fun _w₀ => congrArg HaltingAnchoredGluedSummitSemanticReport.tracked hsr) ?_
  exact fun w₀ =>
    congrArg (fun r : HaltingAnchoredGluedSummitSemanticReport h hF =>
        (⟨r⟩ : NEMSHaltingAnchoredSemanticReportCertificate h hF w₀)) hsr

/-! ## Authoritative report: cascade / tracked agree with bundle via `summit_agrees` -/

theorem cascade_of_agreed_eq_authoritative (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    (agreed_summit b).cascade = (halting_anchored_glued_summit_semantic_report h hF).cascade :=
  congrArg HaltingAnchoredGluedSummitSemanticReport.cascade b.summit_agrees

theorem tracked_of_agreed_eq_authoritative (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    (agreed_summit b).tracked = (halting_anchored_glued_summit_semantic_report h hF).tracked :=
  congrArg HaltingAnchoredGluedSummitSemanticReport.tracked b.summit_agrees

/-- **`cascade_of`** at the canonical index, from **`summit_agrees`** alone (**`Prop`** layer on `sc`). -/
theorem cascade_of_to_indexed_canonical_eq_authoritative_cascade
    (sc : NEMSHaltingSummitSemanticCertificate h hF)
    (hag : sc.summitTracked = halting_anchored_glued_summit_semantic_report h hF) :
    cascade_of (to_indexed_canonical_certificate sc) =
      (halting_anchored_glued_summit_semantic_report h hF).cascade :=
  congrArg HaltingAnchoredGluedSummitSemanticReport.cascade hag

theorem cascade_of_ofSummitCert_eq_authoritative_cascade
    (sc : NEMSHaltingSummitSemanticCertificate h hF)
    (hag : sc.summitTracked = halting_anchored_glued_summit_semantic_report h hF) :
    cascade_of (ofSummitCert w sc) =
      (halting_anchored_glued_summit_semantic_report h hF).cascade :=
  congrArg HaltingAnchoredGluedSummitSemanticReport.cascade hag

theorem cascade_of_indexed_canonical_eq_authoritative_cascade (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    cascade_of (indexed_canonical_certificate b) =
      (halting_anchored_glued_summit_semantic_report h hF).cascade :=
  congrArg HaltingAnchoredGluedSummitSemanticReport.cascade b.summit_agrees

theorem cascade_of_indexed_eq_authoritative_cascade (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    cascade_of (indexed_certificate w b) =
      (halting_anchored_glued_summit_semantic_report h hF).cascade :=
  congrArg HaltingAnchoredGluedSummitSemanticReport.cascade b.summit_agrees

theorem tracked_of_indexed_canonical_eq_authoritative_tracked (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    tracked_of (indexed_canonical_certificate b) =
      (halting_anchored_glued_summit_semantic_report h hF).tracked :=
  congrArg HaltingAnchoredGluedSummitSemanticReport.tracked b.summit_agrees

theorem tracked_of_indexed_eq_authoritative_tracked (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    tracked_of (indexed_certificate w b) =
      (halting_anchored_glued_summit_semantic_report h hF).tracked :=
  congrArg HaltingAnchoredGluedSummitSemanticReport.tracked b.summit_agrees

/-! ## Coherence: when `lawfulCascade` matches the authoritative report -/

/-- Bundle **`lawfulCascade`** matches the Layer-A component of the authoritative halting report. **`mkStandard`**
    satisfies this **`rfl`**; arbitrary bundles may omit it. -/
def MasterBundleCascadeCoherent (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) : Prop :=
  b.lawfulCascade = (halting_anchored_glued_summit_semantic_report h hF).cascade

theorem master_bundle_cascade_coherent_mkStandard :
    MasterBundleCascadeCoherent (mkStandard h hF) :=
  rfl

theorem lawfulCascade_eq_cascade_of_indexed_canonical (b : HaltingAnchoredFaithfulSummitMasterBundle h hF)
    (hc : MasterBundleCascadeCoherent b) :
    b.lawfulCascade = cascade_of (indexed_canonical_certificate b) :=
  hc.trans (congrArg HaltingAnchoredGluedSummitSemanticReport.cascade b.summit_agrees).symm

theorem lawfulCascade_eq_cascade_of_indexed (b : HaltingAnchoredFaithfulSummitMasterBundle h hF)
    (hc : MasterBundleCascadeCoherent b) :
    b.lawfulCascade = cascade_of (indexed_certificate w b) :=
  hc.trans (congrArg HaltingAnchoredGluedSummitSemanticReport.cascade b.summit_agrees).symm

/-- **`as_fourfold_core`** Layer-A conjunct equals **`cascade_of`** on the canonical indexed certificate
    when the bundle is cascade-coherent (inlined **`hc` · `summit_agrees`** chain — avoids elaborating
    **`lawfulCascade_eq_cascade_of_indexed_canonical`**, which can pick up stuck universes in some contexts). -/
theorem as_fourfold_lawfulCascade_eq_cascade_of_indexed_canonical
    (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) (hc : MasterBundleCascadeCoherent b) :
    (as_fourfold_core b).1 = cascade_of (indexed_canonical_certificate b) :=
  (as_fourfold_core_lawfulCascade b).trans
    (hc.trans (congrArg HaltingAnchoredGluedSummitSemanticReport.cascade b.summit_agrees).symm)

theorem as_fourfold_lawfulCascade_eq_cascade_of_indexed
    (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) (hc : MasterBundleCascadeCoherent b) :
    (as_fourfold_core b).1 = cascade_of (indexed_certificate w b) :=
  (as_fourfold_core_lawfulCascade b).trans
    (hc.trans (congrArg HaltingAnchoredGluedSummitSemanticReport.cascade b.summit_agrees).symm)

/-! ## Normative outer recovery (index only; not from `summitTracked`) -/

theorem outer_from_indexed_canonical (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    outer_from_index faithful_nems_semantic_remainder_at_unit (indexed_canonical_certificate b) =
      faithful_nems_semantic_remainder_at_unit :=
  rfl

theorem outer_from_indexed (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    outer_from_index w (indexed_certificate w b) = w :=
  rfl

theorem outer_from_reindexed_master (e : w₁ = w₂) (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    outer_from_index w₂ (reindex e (indexed_certificate w₁ b)) = w₂ :=
  rfl

theorem outer_from_master_reindex_arbitrary (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    outer_from_index w₂ (reindex_arbitrary w₂ (indexed_certificate w₁ b)) = w₂ :=
  rfl

/-- At the canonical index, **`outer_from_index`** returns the **EPIC_018** witness
    **`faithful_nems_semantic_remainder_at_unit`** (`NEMSFaithful.lean`) — normative API citation name. -/
theorem outer_from_indexed_canonical_eq_faithful_nems_remainder
    (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    outer_from_index faithful_nems_semantic_remainder_at_unit (indexed_canonical_certificate b) =
      faithful_nems_semantic_remainder_at_unit :=
  rfl

/-! ## Functoriality in **`summitCert`** (same `summitTracked` payload) -/

theorem agreed_summit_eq_of_bundle_summitCert_eq {b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF}
    (hsc : b₁.summitCert = b₂.summitCert) :
    agreed_summit b₁ = agreed_summit b₂ :=
  congrArg NEMSHaltingSummitSemanticCertificate.summitTracked hsc

theorem indexed_certificate_eq_of_bundle_summitCert_eq {b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF}
    (hsc : b₁.summitCert = b₂.summitCert) :
    indexed_certificate w b₁ = indexed_certificate w b₂ :=
  eq_of_summitTracked_eq (congrArg NEMSHaltingSummitSemanticCertificate.summitTracked hsc)

theorem indexed_canonical_certificate_eq_of_bundle_summitCert_eq
    {b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF}
    (hsc : b₁.summitCert = b₂.summitCert) :
    indexed_canonical_certificate b₁ = indexed_canonical_certificate b₂ :=
  eq_of_summitTracked_eq (congrArg NEMSHaltingSummitSemanticCertificate.summitTracked hsc)

/-! ## Phase C LinkedArchitecture: inherited from any indexed certificate at `(h, hF)` -/

/-- LinkedArchitecture enriched shape at `(h, hF)` — independent of master bundle fields (**`Phase C`**). -/
theorem linked_enriched_of_master_bundle (_b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    linkedCorpusArchitecture.EnrichedIrreducibility :=
  halting_anchored_glued_summit_linked_enriched h hF

/-- Same conclusion via the canonical indexed certificate (alias for citation ergonomics). -/
theorem linked_enriched_of_master_indexed_canonical (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    linkedCorpusArchitecture.EnrichedIrreducibility :=
  linked_enriched_of_master_bundle b

/-- Same conclusion via an arbitrary outer index (alias for citation ergonomics). -/
theorem linked_enriched_of_master_indexed
    (_b : HaltingAnchoredFaithfulSummitMasterBundle h hF)
    (_w : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit) :
    linkedCorpusArchitecture.EnrichedIrreducibility :=
  halting_anchored_glued_summit_linked_enriched h hF

/-! ## Abbreviation **`halting_anchored_faithful_summit_master_bundle`** (`mkStandard`) -/

theorem agreed_summit_halting_anchored_faithful_summit_master_bundle :
    agreed_summit (halting_anchored_faithful_summit_master_bundle h hF) =
      agreed_summit (mkStandard h hF) :=
  rfl

theorem indexed_canonical_halting_anchored_faithful_summit_master_bundle :
    indexed_canonical_certificate (halting_anchored_faithful_summit_master_bundle h hF) =
      indexed_canonical_certificate (mkStandard h hF) :=
  rfl

theorem indexed_certificate_halting_anchored_faithful_summit_master_bundle
    (w₀ : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit) :
    indexed_certificate w₀ (halting_anchored_faithful_summit_master_bundle h hF) =
      indexed_certificate w₀ (mkStandard h hF) :=
  rfl

theorem mkStandard_eq_halting_anchored_bundle :
    mkStandard h hF = halting_anchored_faithful_summit_master_bundle h hF :=
  mkStandard_eq_halting_anchored_faithful_summit_master_bundle h hF

/-! ## Standard witness (`mkStandard`) — closed transport identities -/

theorem indexed_canonical_mkStandard_eq_standard :
    indexed_canonical_certificate (mkStandard h hF) = standard h hF := by
  rcases mkStandard h hF with ⟨_, _, _, hag⟩
  exact NEMSHaltingAnchoredSemanticReportCertificate.eq_of_summitTracked_eq hag

theorem summitReportOf_indexed_canonical_mkStandard :
    summitReportOf (indexed_canonical_certificate (mkStandard h hF)) =
      halting_anchored_glued_summit_semantic_report h hF :=
  rfl

theorem transport_mkStandard_coherent :
    MasterBundleCascadeCoherent (mkStandard h hF) :=
  master_bundle_cascade_coherent_mkStandard

theorem summitReportOf_indexed_mkStandard (w₀ : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit) :
    summitReportOf (indexed_certificate w₀ (mkStandard h hF)) =
      halting_anchored_glued_summit_semantic_report h hF :=
  rfl

theorem tracked_of_indexed_mkStandard_eq_authoritative_tracked
    (w₀ : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit) :
    tracked_of (indexed_certificate w₀ (mkStandard h hF)) =
      (halting_anchored_glued_summit_semantic_report h hF).tracked :=
  rfl

theorem cascade_of_indexed_mkStandard_eq_authoritative_cascade
    (w₀ : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit) :
    cascade_of (indexed_certificate w₀ (mkStandard h hF)) =
      (halting_anchored_glued_summit_semantic_report h hF).cascade :=
  rfl

theorem indexed_certificate_mkStandard_eq_ofSummitCert
    (w₀ : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit) :
    indexed_certificate w₀ (mkStandard h hF) =
      ofSummitCert w₀ (NEMSHaltingSummitSemanticCertificate.summitStandard h hF) :=
  rfl

theorem summitReportOf_standard_eq_summitReportOf_indexed_canonical_mkStandard :
    summitReportOf (standard h hF) =
      summitReportOf (indexed_canonical_certificate (mkStandard h hF)) :=
  rfl

theorem linked_enriched_of_master_reindexed (_e : w₁ = w₂) (_b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    linkedCorpusArchitecture.EnrichedIrreducibility :=
  halting_anchored_glued_summit_linked_enriched h hF

theorem linked_enriched_of_master_reindex_arbitrary (_b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    linkedCorpusArchitecture.EnrichedIrreducibility :=
  halting_anchored_glued_summit_linked_enriched h hF

/-! ## What transport does **not** determine (explicit interface boundary) -/

/--
  **`summitTracked` / forgetful image** fixes the Phase C report only; it does **not** choose which
  **EPIC_018** proof term indexes **`NEMSHaltingAnchoredSemanticReportCertificate`** — that data lives in
  the **type index** `w` (phantom for the grid, but meaningful for bookkeeping and for **`outer_from_index`**).
-/
theorem indexed_certificate_ext_param (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    (indexed_certificate w₁ b).summitTracked = (indexed_certificate w₂ b).summitTracked :=
  rfl

end NEMSSemanticFaithfulTransport

end AdequacyArchitecture.Instances
