/-
  **SPEC_025 — Phase E:** **certificate transport** — explicit morphisms between indexed summit certificates
  and the underlying summit report, **without** a global `∧` of lawful and EPIC_018 layers.

  * **Forgetful leg** (`summitReportOf`): `NEMSHaltingAnchoredSemanticReportCertificate → HaltingAnchoredGluedSummitSemanticReport`.  
  * **Reindexing** (`reindex`): change the outer witness tag along **any** proof `w₁ = w₂`; the witness is
    **not used** in the certificate term (` ⟨c.summitTracked⟩ `), matching the **phantom-index** design.  
  * **Section** (`ofSummit_summitReportOf`): every certificate is uniquely determined by its summit report at
    a **fixed** index (`certificate_ext`). **Path transport:** `ofSummit_summitReportOf_reindex` for `reindex e`.

  **Honesty:** outer `SemanticRemainder` still arrives only via the **index** or detached lemmas such as
  **`faithful_nems_semantic_remainder_at_unit`**; transport does not infer remainder from `summitTracked`.

  **LinkedArchitecture:** inner enriched / remainder-existential shape from Phase C depends only on
  `(h, hF)`, hence is available from any certificate over the same summit hypotheses.

  **Phase F / master `Type` bundle:** see **`NEMSSemanticReportCertificate.lean`** (**`halting_anchored_canonical_certificate_summit_agreement`**, **`to_indexed_canonical_certificate`**) and **`NEMSSemanticFaithfulSummitMaster.lean`**
  (**`HaltingAnchoredFaithfulSummitMasterBundle`**, no remainder field). **Phase G:** master-bundle transport — **`NEMSSemanticFaithfulTransport.lean`**. **SPEC_025** § *Official composition API*.
-/

import AdequacyArchitecture.Instances.NEMSSemanticReportCertificate

namespace AdequacyArchitecture.Instances

open AdequacyArchitecture.Lawful
open ReflexiveArchitecture.Instances
open NemS.Framework
open NemS
open NemS.Physical

namespace NEMSHaltingAnchoredSemanticReportCertificate

variable {h : HFinalFrameworkWithNEMAnchoredGlue} {hF : h.F₀ = haltingFramework}
variable {w w₁ w₂ w₃ : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit}

/-- **Forgetful morphism** to the halting-anchored summit report (ignores which outer witness indexes). -/
abbrev summitReportOf (c : NEMSHaltingAnchoredSemanticReportCertificate h hF w) :
    HaltingAnchoredGluedSummitSemanticReport h hF :=
  c.summitTracked

/-- **Outer index** as the right leg of the observation span (not derived from `summitTracked`). -/
abbrev outerWitnessOf (_c : NEMSHaltingAnchoredSemanticReportCertificate h hF w) :
    faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit :=
  w

/-- Repackage the same summit report at another outer witness (equality is **logical** discipline; the
    term ignores which `SemanticRemainder` proof tags the family). -/
theorem reindex (_ : w₁ = w₂) (c : NEMSHaltingAnchoredSemanticReportCertificate h hF w₁) :
    NEMSHaltingAnchoredSemanticReportCertificate h hF w₂ :=
  ⟨c.summitTracked⟩

/-- The same field suffices at **any** index (phantom witness / tabulation discipline). -/
theorem reindex_arbitrary (w₂ : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (c : NEMSHaltingAnchoredSemanticReportCertificate h hF w) :
    NEMSHaltingAnchoredSemanticReportCertificate h hF w₂ :=
  ⟨c.summitTracked⟩

theorem summitReportOf_reindex (e : w₁ = w₂)
    (c : NEMSHaltingAnchoredSemanticReportCertificate h hF w₁) :
    summitReportOf (reindex e c) = summitReportOf c :=
  rfl

theorem summitReportOf_reindex_arbitrary (w' : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (c : NEMSHaltingAnchoredSemanticReportCertificate h hF w) :
    summitReportOf (reindex_arbitrary w' c) = summitReportOf c :=
  rfl

/-- **`reindex` along `e : w₁ = w₂`** agrees with **`reindex_arbitrary w₂`** on **`w₁`**-tagged certs (phantom index). -/
theorem reindex_eq_reindex_arbitrary (e : w₁ = w₂)
    (c : NEMSHaltingAnchoredSemanticReportCertificate h hF w₁) :
    reindex e c = reindex_arbitrary w₂ c :=
  rfl

/-- Functoriality: composing paths composes **`reindex`** (still **`rfl`** on `summitTracked`). -/
theorem reindex_trans (e₁₂ : w₁ = w₂) (e₂₃ : w₂ = w₃)
    (c : NEMSHaltingAnchoredSemanticReportCertificate h hF w₁) :
    reindex (e₁₂.trans e₂₃) c = reindex e₂₃ (reindex e₁₂ c) :=
  rfl

/-- After **`reindex`**, the **type-index** outer witness is the destination tag **`w₂`** (not `summitTracked`). -/
theorem outerWitnessOf_reindex (e : w₁ = w₂)
    (c : NEMSHaltingAnchoredSemanticReportCertificate h hF w₁) :
    outerWitnessOf (reindex e c) = w₂ :=
  rfl

theorem outerWitnessOf_reindex_arbitrary (w' : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (c : NEMSHaltingAnchoredSemanticReportCertificate h hF w) :
    outerWitnessOf (reindex_arbitrary w' c) = w' :=
  rfl

theorem tracked_of_reindex (e : w₁ = w₂)
    (c : NEMSHaltingAnchoredSemanticReportCertificate h hF w₁) :
    tracked_of (reindex e c) = tracked_of c :=
  rfl

theorem cascade_of_reindex (e : w₁ = w₂)
    (c : NEMSHaltingAnchoredSemanticReportCertificate h hF w₁) :
    cascade_of (reindex e c) = cascade_of c :=
  rfl

theorem tracked_of_reindex_arbitrary (w' : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (c : NEMSHaltingAnchoredSemanticReportCertificate h hF w) :
    tracked_of (reindex_arbitrary w' c) = tracked_of c :=
  rfl

theorem cascade_of_reindex_arbitrary (w' : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (c : NEMSHaltingAnchoredSemanticReportCertificate h hF w) :
    cascade_of (reindex_arbitrary w' c) = cascade_of c :=
  rfl

/-- **`outer_from_index`** tracks the **destination** tag after **`reindex`** (not `summitTracked`). -/
theorem outer_from_index_reindex (e : w₁ = w₂)
    (c : NEMSHaltingAnchoredSemanticReportCertificate h hF w₁) :
    outer_from_index w₂ (reindex e c) = w₂ :=
  rfl

theorem outer_from_index_reindex_arbitrary (w' : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (c : NEMSHaltingAnchoredSemanticReportCertificate h hF w) :
    outer_from_index w' (reindex_arbitrary w' c) = w' :=
  rfl

/-- **`outer_from_index`** with the certificate’s own tabulation tag. -/
theorem outer_from_index_outerWitnessOf (c : NEMSHaltingAnchoredSemanticReportCertificate h hF w) :
    outer_from_index (outerWitnessOf c) c = outerWitnessOf c :=
  rfl

/-! ### Reindex as a (proof-relevant) **groupoid** on the phantom index -/

theorem reindex_refl (c : NEMSHaltingAnchoredSemanticReportCertificate h hF w) :
    reindex rfl c = c :=
  rfl

theorem reindex_arbitrary_self (c : NEMSHaltingAnchoredSemanticReportCertificate h hF w) :
    reindex_arbitrary w c = c :=
  rfl

theorem reindex_reindex_symm (e : w₁ = w₂) (c : NEMSHaltingAnchoredSemanticReportCertificate h hF w₁) :
    reindex e.symm (reindex e c) = c :=
  rfl

theorem reindex_symm_reindex (e : w₁ = w₂) (c : NEMSHaltingAnchoredSemanticReportCertificate h hF w₂) :
    reindex e (reindex e.symm c) = c :=
  rfl

theorem reindex_arbitrary_reindex (e : w₁ = w₂)
    (c : NEMSHaltingAnchoredSemanticReportCertificate h hF w₁) :
    reindex_arbitrary w₃ (reindex e c) = reindex_arbitrary w₃ c :=
  rfl

theorem reindex_arbitrary_reindex_arbitrary (w' w'' : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (c : NEMSHaltingAnchoredSemanticReportCertificate h hF w) :
    reindex_arbitrary w'' (reindex_arbitrary w' c) = reindex_arbitrary w'' c :=
  rfl

theorem certificate_ext (c₁ c₂ : NEMSHaltingAnchoredSemanticReportCertificate h hF w)
    (hst : c₁.summitTracked = c₂.summitTracked) : c₁ = c₂ := by
  cases c₁
  cases c₂
  cases hst
  rfl

theorem eq_of_summitTracked (rep : HaltingAnchoredGluedSummitSemanticReport h hF)
    (c : NEMSHaltingAnchoredSemanticReportCertificate h hF w)
    (hst : c.summitTracked = rep) : c = ofSummit rep := by
  cases c
  cases hst
  rfl

theorem ofSummit_summitReportOf (c : NEMSHaltingAnchoredSemanticReportCertificate h hF w) :
    ofSummit (summitReportOf c) = c := by
  rcases c with ⟨t⟩
  rfl

/-- Section for **`reindex`** along **`e : w₁ = w₂`** (destination tag **`w₂`**). -/
theorem ofSummit_summitReportOf_reindex (e : w₁ = w₂)
    (c : NEMSHaltingAnchoredSemanticReportCertificate h hF w₁) :
    @ofSummit h hF w₂ (summitReportOf (reindex e c)) = reindex e c := by
  rcases c with ⟨t⟩
  rfl

/-- Same **outer** index `w`: forgetful image determines the certificate (`summitReportOf` = **`.summitTracked`**). -/
theorem eq_of_summitReportOf_eq (c₁ c₂ : NEMSHaltingAnchoredSemanticReportCertificate h hF w)
    (hsr : summitReportOf c₁ = summitReportOf c₂) : c₁ = c₂ :=
  eq_of_summitTracked_eq hsr

/-- Section for **`reindex_arbitrary`**: same forgetful image, destination index in **`@ofSummit`**. -/
theorem ofSummit_summitReportOf_reindex_arbitrary
    (w' : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (c : NEMSHaltingAnchoredSemanticReportCertificate h hF w) :
    @ofSummit h hF w' (summitReportOf (reindex_arbitrary w' c)) = reindex_arbitrary w' c := by
  rcases c with ⟨t⟩
  rfl

theorem to_summit_only_reindex (e : w₁ = w₂)
    (c : NEMSHaltingAnchoredSemanticReportCertificate h hF w₁) :
    to_summit_only (reindex e c) = to_summit_only c :=
  rfl

theorem to_summit_only_reindex_arbitrary (w' : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (c : NEMSHaltingAnchoredSemanticReportCertificate h hF w) :
    to_summit_only (reindex_arbitrary w' c) = to_summit_only c :=
  rfl

/-- **`reindex`** is **injective** on `summitTracked` (phantom index carries no extra data). -/
theorem eq_of_reindex_eq (e : w₁ = w₂)
    (c₁ c₂ : NEMSHaltingAnchoredSemanticReportCertificate h hF w₁)
    (hr : reindex e c₁ = reindex e c₂) : c₁ = c₂ :=
  eq_of_summitTracked_eq (congrArg NEMSHaltingAnchoredSemanticReportCertificate.summitTracked hr)

theorem eq_of_reindex_arbitrary_eq (w' : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (c₁ c₂ : NEMSHaltingAnchoredSemanticReportCertificate h hF w)
    (hr : reindex_arbitrary w' c₁ = reindex_arbitrary w' c₂) : c₁ = c₂ :=
  eq_of_summitTracked_eq (congrArg NEMSHaltingAnchoredSemanticReportCertificate.summitTracked hr)

theorem standard_summitReport (h : HFinalFrameworkWithNEMAnchoredGlue) (hF : h.F₀ = haltingFramework) :
    summitReportOf (standard h hF) = halting_anchored_glued_summit_semantic_report h hF :=
  rfl

/-- **Phase C** linked reporting depends only on `(h, hF)`; any certificate over those hypotheses
    inherits the same **EnrichedIrreducibility** conclusion. -/
theorem linked_enriched_of_certificate (_c : NEMSHaltingAnchoredSemanticReportCertificate h hF w) :
    linkedCorpusArchitecture.EnrichedIrreducibility :=
  halting_anchored_glued_summit_linked_enriched h hF

/-- Citation alias: reindexing does not change **`(h, hF)`**, hence the same Phase C enrichment. -/
theorem linked_enriched_of_reindex (_e : w₁ = w₂)
    (_c : NEMSHaltingAnchoredSemanticReportCertificate h hF w₁) :
    linkedCorpusArchitecture.EnrichedIrreducibility :=
  halting_anchored_glued_summit_linked_enriched h hF

theorem linked_enriched_of_reindex_arbitrary
    (_w' : faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit)
    (_c : NEMSHaltingAnchoredSemanticReportCertificate h hF w) :
    linkedCorpusArchitecture.EnrichedIrreducibility :=
  halting_anchored_glued_summit_linked_enriched h hF

end NEMSHaltingAnchoredSemanticReportCertificate

end AdequacyArchitecture.Instances
