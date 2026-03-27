/-
  **SPEC_032 HM5_RK2 — tagged halting summit staging (enlarged `B_γ`).**

  **Context (`SPEC_032_HM4_K9N`):** at fixed **`(h, hF)`**, **`HaltingAnchoredFaithfulSummitMasterBundle h hF`** is subsingleton up to **`mkStandard`** —
  no honest **varying** **`b : γ → HaltingMaster`** at the **untyped** master fiber.

  **This slice:** carry **extra** data on the staging type (**`CorpusStrataCarrier` tag** + summit bundle). Law X projects **`bundle`**; the **graph** **`i`** pairs a per-point tag **`τ`** with **`b`**. Then **`effectiveProj = b`** (same FE-3 carrier as plain prodGraph on the bundle side), while **staging** values can differ **only in **`tag`** even when every **`bundle`** is **`mkStandard`**.

  **Deliverable map:** **`TaggedHaltingSummitMasterStaging`**, **`taggedSummitStaging_toMaster`**, **`nemsSummitCarrierBridgeData_taggedGraph`**, **`nemsSummitCarrierBridge_taggedGraph_effectiveProj`**, **`nemsFe3IndexedPhantomOps_carrier_taggedGraph_eq_pullbackAlongDom_b`**, tag nontriviality lemmas.

  **PI1 / SA1 (`SPEC_032_HM5_RK2` integration):** same **`NemsSummitCarrierBridgeCompareAlignment`** / section-aware packs as **`SPEC_032_CB1`**, instantiated at **`br := nemsSummitCarrierBridgeData_taggedGraph`**. **`effectiveProj`** still equals **`b`**, so compare–host factorization is **identical** to prodGraph on the NEMS **indexed** slot; **new** content is **`B_γ⋆`** / **`i`** typing (tagged graph), not a different **`haltingAnchoredNems`** pullback.

  **Semantic expressivity (short):** Law X **`summitReportOf` / `agreed_summit`** still factors through **`bundle = taggedSummitStaging_toMaster`** — **no** extra phantom or summit certificate field. Tags are **carrier bookkeeping** on **`B_γ⋆`** unless a downstream law **mentions** **`tag`** in its **`indexed`** / reporting interface.

  **`SPEC_032_HM6_QT3`:** sharp **tag-blindness** at **`taggedSummitStaging_toMaster` + FE-3 pullback** — **`taggedSummitStaging_toMaster_eq_iff_bundle_eq`**, **`nemsFe3IndexedPhantomOps_carrier_taggedGraph_eq_of_same_b`**, **`nemsFe3IndexedPhantomOps_carrier_taggedGraph_summitReportOf_eq_of_same_b`**; note **`SPEC_032_HM6_QT3_TAG_BLINDNESS_FE3_LAYER.md`**.

  **`SPEC_032_HM7_VW2`:** **positive footnote** — minimal **`BranchGenericSemanticTransport.IndexedPhantomCertificateOps`** on **`B_γ⋆`** whose **`agreedSummit` / `indexed`** **read `tag`** (not **NEMS**); note **`SPEC_032_HM7_VW2_TAG_WITNESS_BRANCH_GENERIC_OPS.md`**.
-/

import AdequacyArchitecture.Instances.CorpusDischarge
import AdequacyArchitecture.Instances.NemsSummitCarrierBridge

namespace AdequacyArchitecture.Instances

open HaltingAnchoredFaithfulSummitMasterBundle
open NemS.Framework
open NemS.Physical
open AdequacyArchitecture
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open AdequacyArchitecture.Portability
open AdequacyArchitecture.Portability.BranchGenericSemanticTransport
open NEMSHaltingAnchoredSemanticReportCertificate

/--
  **Enlarged staging type (`B_γ⋆` pattern):** corpus stratum tag **plus** halting anchored faithful summit master bundle.

  Variation in **`tag`** is **independent** of **`SPEC_032_HM4_K9N`** collapse on **`bundle`**.
-/
structure TaggedHaltingSummitMasterStaging (h : HFinalFrameworkWithNEMAnchoredGlue)
    (hF : h.F₀ = haltingFramework) : Type where
  tag : CorpusStrataCarrier
  bundle : HaltingAnchoredFaithfulSummitMasterBundle h hF

variable {h : HFinalFrameworkWithNEMAnchoredGlue} {hF : h.F₀ = haltingFramework}

/-- Law-X–style forgetful map to the **`SPEC_025`** master bundle. -/
def taggedSummitStaging_toMaster (s : TaggedHaltingSummitMasterStaging h hF) : HaltingMaster h hF :=
  s.bundle

theorem taggedSummit_staging_ne_of_tag_ne
    (t s : TaggedHaltingSummitMasterStaging h hF) (hne : t.tag ≠ s.tag) : t ≠ s := fun heq =>
  hne (congrArg TaggedHaltingSummitMasterStaging.tag heq)

theorem corpusStrataCarrier_zero_ne_one : (0 : CorpusStrataCarrier) ≠ 1 := by decide

theorem taggedSummit_staging_mkStandard_zero_ne_one :
    (⟨(0 : CorpusStrataCarrier), mkStandard h hF⟩ : TaggedHaltingSummitMasterStaging h hF) ≠
      ⟨(1 : CorpusStrataCarrier), mkStandard h hF⟩ :=
  taggedSummit_staging_ne_of_tag_ne _ _ corpusStrataCarrier_zero_ne_one

variable {γ α : Type}

/--
  **Graph section:** tags **`τ`** and summit maps **`b`** assemble a map **`γ → TaggedHaltingSummitMasterStaging`**.
-/
def taggedSummitGraphSection (τ : γ → CorpusStrataCarrier) (b : γ → HaltingMaster h hF) :
    γ → TaggedHaltingSummitMasterStaging h hF :=
  fun x => ⟨τ x, b x⟩

/--
  **Tagged graph bridge:** **`B_γ`** is **`TaggedHaltingSummitMasterStaging`**, **`σ.proj = taggedSummitStaging_toMaster`**
  (**defeq** to **`TaggedHaltingSummitMasterStaging.bundle`**).
-/
def nemsSummitCarrierBridgeData_taggedGraph (repr : CertifiedFrontierRepresentation γ α)
    (τ : γ → CorpusStrataCarrier) (b : γ → HaltingMaster h hF) : NemsSummitCarrierBridgeData h hF repr where
  B_γ := TaggedHaltingSummitMasterStaging h hF
  i := taggedSummitGraphSection τ b
  σ := nemsFe3SummitBundleCompareSection_mk h hF taggedSummitStaging_toMaster

theorem nemsSummitCarrierBridge_taggedGraph_effectiveProj (repr : CertifiedFrontierRepresentation γ α)
    (τ : γ → CorpusStrataCarrier) (b : γ → HaltingMaster h hF) :
    (nemsSummitCarrierBridgeData_taggedGraph repr τ b).effectiveProj = b := by
  funext x
  rfl

/--
  **FE-3 on `γ`** along the tagged graph bridge matches **pullback along the same **`b`**** as **plain prodGraph**
  (**`SPEC_032_CB1`** corollary shape).
-/
theorem nemsFe3IndexedPhantomOps_carrier_taggedGraph_eq_pullbackAlongDom_b
    (repr : CertifiedFrontierRepresentation γ α) (τ : γ → CorpusStrataCarrier) (b : γ → HaltingMaster h hF) :
    indexedPhantomCertificateOps_pullbackAlongDom
        (nemsSummitCarrierBridgeData_taggedGraph repr τ b).effectiveProj
        (@haltingAnchoredNemsIndexedPhantomOps h hF) =
      indexedPhantomCertificateOps_pullbackAlongDom b (@haltingAnchoredNemsIndexedPhantomOps h hF) := by
  rw [nemsSummitCarrierBridge_taggedGraph_effectiveProj]

/-!
### **`SPEC_032_HM6_QT3` — tag-blindness at Law X / FE-3 (obstruction / negative knowledge)**

**Law X on `B_γ⋆`** uses **`taggedSummitStaging_toMaster`**, which **depends only on `bundle`**. The generic **`indexedPhantomCertificateOps_pullbackAlongDom`**
constructor **leaves `summitReportOf` unchanged** (**`BranchGenericSemanticTransport`**). Hence **tag-only** differences on **`TaggedHaltingSummitMasterStaging`**
do **not** alter γ-side pulled-back NEMS ops when **`b`** is fixed — **HM5** remains **staging bookkeeping** at this semantic layer unless a **new** law
feeds **`tag`** into **`indexed`**, **`agreedSummit`**, or a **non-standard** Law X **`proj`**.
-/

theorem taggedSummitStaging_toMaster_eq_iff_bundle_eq (s t : TaggedHaltingSummitMasterStaging h hF) :
    taggedSummitStaging_toMaster s = taggedSummitStaging_toMaster t ↔ s.bundle = t.bundle :=
  Iff.rfl

theorem taggedSummitStaging_agreed_summit_eq_of_bundle_eq (s t : TaggedHaltingSummitMasterStaging h hF)
    (hst : s.bundle = t.bundle) :
    agreed_summit (taggedSummitStaging_toMaster s) = agreed_summit (taggedSummitStaging_toMaster t) :=
  congrArg agreed_summit hst

/--
  **Retag invariance:** any two tag maps **`τ`**, **`τ'`** with the same summit map **`b`** yield **identical** γ-side FE-3 pullbacks.
-/
theorem nemsFe3IndexedPhantomOps_carrier_taggedGraph_eq_of_same_b
    (repr : CertifiedFrontierRepresentation γ α) (τ τ' : γ → CorpusStrataCarrier) (b : γ → HaltingMaster h hF) :
    indexedPhantomCertificateOps_pullbackAlongDom
        (nemsSummitCarrierBridgeData_taggedGraph repr τ b).effectiveProj
        (@haltingAnchoredNemsIndexedPhantomOps h hF) =
      indexedPhantomCertificateOps_pullbackAlongDom
        (nemsSummitCarrierBridgeData_taggedGraph repr τ' b).effectiveProj
        (@haltingAnchoredNemsIndexedPhantomOps h hF) := by
  simp_rw [nemsSummitCarrierBridge_taggedGraph_effectiveProj]

/--
  **`summitReportOf`** on those pullbacks is **unchanged** under retagging (**`summitReportOf`** is not reindexed by bundle-side pullback — **Phase D**).
-/
theorem nemsFe3IndexedPhantomOps_carrier_taggedGraph_summitReportOf_eq_of_same_b
    (repr : CertifiedFrontierRepresentation γ α) (τ τ' : γ → CorpusStrataCarrier) (b : γ → HaltingMaster h hF) :
    (indexedPhantomCertificateOps_pullbackAlongDom
        (nemsSummitCarrierBridgeData_taggedGraph repr τ b).effectiveProj
        (@haltingAnchoredNemsIndexedPhantomOps h hF)).summitReportOf =
      (indexedPhantomCertificateOps_pullbackAlongDom
        (nemsSummitCarrierBridgeData_taggedGraph repr τ' b).effectiveProj
        (@haltingAnchoredNemsIndexedPhantomOps h hF)).summitReportOf :=
  congrArg IndexedPhantomCertificateOps.summitReportOf
    (nemsFe3IndexedPhantomOps_carrier_taggedGraph_eq_of_same_b repr τ τ' b)

/-!
### **`SPEC_032_PI1`** on tagged graph — compare / **`hostBundleMap`** triangle
-/

/--
  **Tagged graph + identity compare:** same **`hostBundleMap := b`** pattern as **`prodGraph`** (**`SPEC_032_PI1`**).
-/
def nemsSummitCarrierBridgeCompareAlignment_taggedGraph_of_id_compare {γ : Type}
    {repr : CertifiedFrontierRepresentation γ γ} (hπ : repr.π = id)
    (τ : γ → CorpusStrataCarrier) (b : γ → HaltingMaster h hF) :
    NemsSummitCarrierBridgeCompareAlignment (nemsSummitCarrierBridgeData_taggedGraph repr τ b) where
  hostBundleMap := b
  effectiveProj_eq_host_comp_compare := fun x => by
    rw [congrFun (nemsSummitCarrierBridge_taggedGraph_effectiveProj repr τ b) x]
    exact (congrArg b (show repr.π x = x from by simpa [Function.id_def] using congrFun hπ x)).symm

/--
  **Tagged graph + constant compare:** **`b x = m`**, **`hostBundleMap := fun _ => m`** (e.g. **IC CS-3** shape).
-/
def nemsSummitCarrierBridgeCompareAlignment_taggedGraph_of_constant_compare
    {γ α : Type} {repr : CertifiedFrontierRepresentation γ α}
    (c : α) (_hπ : ∀ x : γ, repr.π x = c)
    (m : HaltingMaster h hF)
    (τ : γ → CorpusStrataCarrier) (b : γ → HaltingMaster h hF)
    (hb : ∀ x : γ, b x = m) :
    NemsSummitCarrierBridgeCompareAlignment (nemsSummitCarrierBridgeData_taggedGraph repr τ b) where
  hostBundleMap := fun _ => m
  effectiveProj_eq_host_comp_compare := fun x => by
    rw [congrFun (nemsSummitCarrierBridge_taggedGraph_effectiveProj repr τ b) x, hb x]

/--
  **PI1 — π-then-host factorization** for tagged graph, **`repr.π = id`**.
-/
theorem nemsFe3IndexedPhantomOps_taggedGraph_align_factors_through_compare_then_host_of_id_compare
    {γ : Type} {repr : CertifiedFrontierRepresentation γ γ} (hπ : repr.π = id)
    (τ : γ → CorpusStrataCarrier) (b : γ → HaltingMaster h hF) :
    indexedPhantomCertificateOps_pullbackAlongDom
        (nemsSummitCarrierBridgeData_taggedGraph repr τ b).effectiveProj
        (@haltingAnchoredNemsIndexedPhantomOps h hF) =
      indexedPhantomCertificateOps_pullbackAlongDom repr.π
        (indexedPhantomCertificateOps_pullbackAlongDom b (@haltingAnchoredNemsIndexedPhantomOps h hF)) :=
  nemsFe3IndexedPhantomOps_pullbackAlongDom_align_factors_through_compare_then_host _
    (nemsSummitCarrierBridgeCompareAlignment_taggedGraph_of_id_compare hπ τ b)

/--
  **PI1 — π-then-host factorization** for tagged graph, constant **`π`** + pointwise constant **`b`**.
-/
theorem nemsFe3IndexedPhantomOps_taggedGraph_align_factors_through_compare_then_host_of_constant_compare
    {γ α : Type} {repr : CertifiedFrontierRepresentation γ α}
    (c : α) (hπ : ∀ x : γ, repr.π x = c) (m : HaltingMaster h hF)
    (τ : γ → CorpusStrataCarrier) (b : γ → HaltingMaster h hF) (hb : ∀ x : γ, b x = m) :
    indexedPhantomCertificateOps_pullbackAlongDom
        (nemsSummitCarrierBridgeData_taggedGraph repr τ b).effectiveProj
        (@haltingAnchoredNemsIndexedPhantomOps h hF) =
      indexedPhantomCertificateOps_pullbackAlongDom repr.π
        (indexedPhantomCertificateOps_pullbackAlongDom (fun _ : α => m) (@haltingAnchoredNemsIndexedPhantomOps h hF)) :=
  nemsFe3IndexedPhantomOps_pullbackAlongDom_align_factors_through_compare_then_host _
    (nemsSummitCarrierBridgeCompareAlignment_taggedGraph_of_constant_compare c hπ m τ b hb)

/-!
### **`SPEC_032_SA1`** on tagged graph — section-aware packs
-/

theorem nemsSummitSectionAware_pack_taggedGraph_isPullback_bridge_v5_forgetfulOnCarrier
    {γ α : Type} {P : AdequacyPredicates γ} {B : BurdenPredicates γ}
    (repr : CertifiedFrontierRepresentation γ α) (hdisp : repr.IsPullbackDisplay P B)
    (τ : γ → CorpusStrataCarrier) (b : γ → HaltingMaster h hF) :
    AbsoluteFrontierRawS1 P B ∧
      indexedPhantomCertificateOps_pullbackAlongDom
          (nemsSummitCarrierBridgeData_taggedGraph repr τ b).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF) =
        indexedPhantomCertificateOps_pullbackAlongDom (nemsSummitCarrierBridgeData_taggedGraph repr τ b).i
          (indexedPhantomCertificateOps_pullbackAlongDom (nemsSummitCarrierBridgeData_taggedGraph repr τ b).σ.proj
            (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      ForgetfulIndexedCoherent
        (indexedPhantomCertificateOps_pullbackAlongDom
          (nemsSummitCarrierBridgeData_taggedGraph repr τ b).effectiveProj (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      ForgetfulAgreementInjects
        (indexedPhantomCertificateOps_pullbackAlongDom
          (nemsSummitCarrierBridgeData_taggedGraph repr τ b).effectiveProj (@haltingAnchoredNemsIndexedPhantomOps h hF)) := by
  let br := nemsSummitCarrierBridgeData_taggedGraph repr τ b
  constructor
  · exact absoluteFrontierRawS1_of_valid_certifiedFrontierRepresentation repr hdisp
  constructor
  · exact nemsFe3IndexedPhantomOps_carrier_bridge_induces_fe3 br
  constructor
  · exact forgetfulIndexedCoherent_of_indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj _
      haltingAnchoredNems_forget_coherent
  · exact forgetfulAgreementInjects_of_indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj _
      haltingAnchoredNems_forget_injects

theorem nemsSummitSectionAware_pack_taggedGraph_isPullback_bridge_v5_forgetfulOnCarrier_injectiveCompareLift
    {γ α : Type} {P : AdequacyPredicates γ} {B : BurdenPredicates γ}
    (repr : CertifiedFrontierRepresentation γ α)
    (hdisp : repr.IsPullbackDisplay P B) (hInj : repr.HasInjectiveCompare)
    (τ : γ → CorpusStrataCarrier) (b : γ → HaltingMaster h hF) :
    AbsoluteFrontierRawS1 P B ∧
      indexedPhantomCertificateOps_pullbackAlongDom
          (nemsSummitCarrierBridgeData_taggedGraph repr τ b).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF) =
        indexedPhantomCertificateOps_pullbackAlongDom (nemsSummitCarrierBridgeData_taggedGraph repr τ b).i
          (indexedPhantomCertificateOps_pullbackAlongDom (nemsSummitCarrierBridgeData_taggedGraph repr τ b).σ.proj
            (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      ForgetfulIndexedCoherent
        (indexedPhantomCertificateOps_pullbackAlongDom
          (nemsSummitCarrierBridgeData_taggedGraph repr τ b).effectiveProj (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      ForgetfulAgreementInjects
        (indexedPhantomCertificateOps_pullbackAlongDom
          (nemsSummitCarrierBridgeData_taggedGraph repr τ b).effectiveProj (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      Function.Injective (compareLiftAccountAlong repr.π) := by
  let br := nemsSummitCarrierBridgeData_taggedGraph repr τ b
  constructor
  · exact absoluteFrontierRawS1_of_valid_certifiedFrontierRepresentation repr hdisp
  constructor
  · exact nemsFe3IndexedPhantomOps_carrier_bridge_induces_fe3 br
  constructor
  · exact forgetfulIndexedCoherent_of_indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj _
      haltingAnchoredNems_forget_coherent
  constructor
  · exact forgetfulAgreementInjects_of_indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj _
      haltingAnchoredNems_forget_injects
  · exact CertifiedFrontierRepresentation.compareLiftAccountAlong_injective_of_repr_injective repr hInj

theorem nemsSummitSectionAware_pack_taggedGraph_isPullback_bridge_v5_forgetfulOnCarrier_alignCompareFactor
    {γ α : Type} {P : AdequacyPredicates γ} {B : BurdenPredicates γ}
    (repr : CertifiedFrontierRepresentation γ α) (hdisp : repr.IsPullbackDisplay P B)
    (τ : γ → CorpusStrataCarrier) (b : γ → HaltingMaster h hF)
    (align : NemsSummitCarrierBridgeCompareAlignment (nemsSummitCarrierBridgeData_taggedGraph repr τ b)) :
    AbsoluteFrontierRawS1 P B ∧
      indexedPhantomCertificateOps_pullbackAlongDom
          (nemsSummitCarrierBridgeData_taggedGraph repr τ b).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF) =
        indexedPhantomCertificateOps_pullbackAlongDom (nemsSummitCarrierBridgeData_taggedGraph repr τ b).i
          (indexedPhantomCertificateOps_pullbackAlongDom (nemsSummitCarrierBridgeData_taggedGraph repr τ b).σ.proj
            (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      ForgetfulIndexedCoherent
        (indexedPhantomCertificateOps_pullbackAlongDom
          (nemsSummitCarrierBridgeData_taggedGraph repr τ b).effectiveProj (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      ForgetfulAgreementInjects
        (indexedPhantomCertificateOps_pullbackAlongDom
          (nemsSummitCarrierBridgeData_taggedGraph repr τ b).effectiveProj (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      indexedPhantomCertificateOps_pullbackAlongDom
          (nemsSummitCarrierBridgeData_taggedGraph repr τ b).effectiveProj (@haltingAnchoredNemsIndexedPhantomOps h hF) =
        indexedPhantomCertificateOps_pullbackAlongDom repr.π
          (indexedPhantomCertificateOps_pullbackAlongDom align.hostBundleMap (@haltingAnchoredNemsIndexedPhantomOps h hF)) := by
  let br := nemsSummitCarrierBridgeData_taggedGraph repr τ b
  constructor
  · exact absoluteFrontierRawS1_of_valid_certifiedFrontierRepresentation repr hdisp
  constructor
  · exact nemsFe3IndexedPhantomOps_carrier_bridge_induces_fe3 br
  constructor
  · exact forgetfulIndexedCoherent_of_indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj _
      haltingAnchoredNems_forget_coherent
  constructor
  · exact forgetfulAgreementInjects_of_indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj _
      haltingAnchoredNems_forget_injects
  · exact nemsFe3IndexedPhantomOps_pullbackAlongDom_align_factors_through_compare_then_host br align

theorem nemsSummitSectionAware_pack_taggedGraph_isPullback_bridge_v5_forgetfulOnCarrier_injectiveCompareLift_alignCompareFactor
    {γ α : Type} {P : AdequacyPredicates γ} {B : BurdenPredicates γ}
    (repr : CertifiedFrontierRepresentation γ α)
    (hdisp : repr.IsPullbackDisplay P B) (hInj : repr.HasInjectiveCompare)
    (τ : γ → CorpusStrataCarrier) (b : γ → HaltingMaster h hF)
    (align : NemsSummitCarrierBridgeCompareAlignment (nemsSummitCarrierBridgeData_taggedGraph repr τ b)) :
    AbsoluteFrontierRawS1 P B ∧
      indexedPhantomCertificateOps_pullbackAlongDom
          (nemsSummitCarrierBridgeData_taggedGraph repr τ b).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF) =
        indexedPhantomCertificateOps_pullbackAlongDom (nemsSummitCarrierBridgeData_taggedGraph repr τ b).i
          (indexedPhantomCertificateOps_pullbackAlongDom (nemsSummitCarrierBridgeData_taggedGraph repr τ b).σ.proj
            (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      ForgetfulIndexedCoherent
        (indexedPhantomCertificateOps_pullbackAlongDom
          (nemsSummitCarrierBridgeData_taggedGraph repr τ b).effectiveProj (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      ForgetfulAgreementInjects
        (indexedPhantomCertificateOps_pullbackAlongDom
          (nemsSummitCarrierBridgeData_taggedGraph repr τ b).effectiveProj (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      indexedPhantomCertificateOps_pullbackAlongDom
          (nemsSummitCarrierBridgeData_taggedGraph repr τ b).effectiveProj (@haltingAnchoredNemsIndexedPhantomOps h hF) =
        indexedPhantomCertificateOps_pullbackAlongDom repr.π
          (indexedPhantomCertificateOps_pullbackAlongDom align.hostBundleMap (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      Function.Injective (compareLiftAccountAlong repr.π) := by
  let br := nemsSummitCarrierBridgeData_taggedGraph repr τ b
  constructor
  · exact absoluteFrontierRawS1_of_valid_certifiedFrontierRepresentation repr hdisp
  constructor
  · exact nemsFe3IndexedPhantomOps_carrier_bridge_induces_fe3 br
  constructor
  · exact forgetfulIndexedCoherent_of_indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj _
      haltingAnchoredNems_forget_coherent
  constructor
  · exact forgetfulAgreementInjects_of_indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj _
      haltingAnchoredNems_forget_injects
  constructor
  · exact nemsFe3IndexedPhantomOps_pullbackAlongDom_align_factors_through_compare_then_host br align
  · exact CertifiedFrontierRepresentation.compareLiftAccountAlong_injective_of_repr_injective repr hInj

/-!
### Corpus Level-1 **`id` + mkStandard** — tagged bridge (**HM1** host map unchanged)
-/

abbrev nemsCorpusLevel1Id_taggedGraph_mkStandard (τ : CorpusStrataCarrier → CorpusStrataCarrier) :
    NemsSummitCarrierBridgeData h hF certifiedFrontierRepresentation_corpus_nems_level1_id :=
  nemsSummitCarrierBridgeData_taggedGraph certifiedFrontierRepresentation_corpus_nems_level1_id τ
    (fun _ => HaltingAnchoredFaithfulSummitMasterBundle.mkStandard h hF)

def nemsSummitCarrierBridgeCompareAlignment_corpusLevel1Id_taggedGraph_mkStandard
    (τ : CorpusStrataCarrier → CorpusStrataCarrier) :
    NemsSummitCarrierBridgeCompareAlignment (@nemsCorpusLevel1Id_taggedGraph_mkStandard h hF τ) :=
  nemsSummitCarrierBridgeCompareAlignment_taggedGraph_of_id_compare
    (show certifiedFrontierRepresentation_corpus_nems_level1_id.π = id from rfl) τ
    (fun _ => HaltingAnchoredFaithfulSummitMasterBundle.mkStandard h hF)

theorem nemsSummitSectionAware_pack_corpusLevel1Id_taggedGraph_mkStandard_aligned
    (τ : CorpusStrataCarrier → CorpusStrataCarrier) :
    AbsoluteFrontierRawS1 corpusNemsFin2Adequacy corpusNemsFin2Burden ∧
      indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel1Id_taggedGraph_mkStandard h hF τ).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF) =
        indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel1Id_taggedGraph_mkStandard h hF τ).i
          (indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel1Id_taggedGraph_mkStandard h hF τ).σ.proj
            (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      ForgetfulIndexedCoherent
        (indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel1Id_taggedGraph_mkStandard h hF τ).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      ForgetfulAgreementInjects
        (indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel1Id_taggedGraph_mkStandard h hF τ).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel1Id_taggedGraph_mkStandard h hF τ).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF) =
        indexedPhantomCertificateOps_pullbackAlongDom certifiedFrontierRepresentation_corpus_nems_level1_id.π
          (indexedPhantomCertificateOps_pullbackAlongDom (@nemsHostBundleMap_corpusStrata_mkStandard h hF)
            (@haltingAnchoredNemsIndexedPhantomOps h hF)) := by
  let br := @nemsCorpusLevel1Id_taggedGraph_mkStandard h hF τ
  let align := @nemsSummitCarrierBridgeCompareAlignment_corpusLevel1Id_taggedGraph_mkStandard h hF τ
  constructor
  · exact absoluteFrontierRawS1_of_valid_certifiedFrontierRepresentation
      certifiedFrontierRepresentation_corpus_nems_level1_id certifiedFrontierRepresentation_corpus_nems_level1_id_isPullbackDisplay
  constructor
  · exact nemsFe3IndexedPhantomOps_carrier_bridge_induces_fe3 br
  constructor
  · exact forgetfulIndexedCoherent_of_indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj _
      haltingAnchoredNems_forget_coherent
  constructor
  · exact forgetfulAgreementInjects_of_indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj _
      haltingAnchoredNems_forget_injects
  · exact nemsFe3IndexedPhantomOps_pullbackAlongDom_align_factors_through_compare_then_host br align

theorem nemsSummitSectionAware_pack_corpusLevel1Id_taggedGraph_mkStandard_aligned_injectiveCompareLift
    (τ : CorpusStrataCarrier → CorpusStrataCarrier) :
    AbsoluteFrontierRawS1 corpusNemsFin2Adequacy corpusNemsFin2Burden ∧
      indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel1Id_taggedGraph_mkStandard h hF τ).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF) =
        indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel1Id_taggedGraph_mkStandard h hF τ).i
          (indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel1Id_taggedGraph_mkStandard h hF τ).σ.proj
            (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      ForgetfulIndexedCoherent
        (indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel1Id_taggedGraph_mkStandard h hF τ).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      ForgetfulAgreementInjects
        (indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel1Id_taggedGraph_mkStandard h hF τ).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel1Id_taggedGraph_mkStandard h hF τ).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF) =
        indexedPhantomCertificateOps_pullbackAlongDom certifiedFrontierRepresentation_corpus_nems_level1_id.π
          (indexedPhantomCertificateOps_pullbackAlongDom (@nemsHostBundleMap_corpusStrata_mkStandard h hF)
            (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      Function.Injective (compareLiftAccountAlong certifiedFrontierRepresentation_corpus_nems_level1_id.π) := by
  let br := @nemsCorpusLevel1Id_taggedGraph_mkStandard h hF τ
  let align := @nemsSummitCarrierBridgeCompareAlignment_corpusLevel1Id_taggedGraph_mkStandard h hF τ
  constructor
  · exact absoluteFrontierRawS1_of_valid_certifiedFrontierRepresentation
      certifiedFrontierRepresentation_corpus_nems_level1_id certifiedFrontierRepresentation_corpus_nems_level1_id_isPullbackDisplay
  constructor
  · exact nemsFe3IndexedPhantomOps_carrier_bridge_induces_fe3 br
  constructor
  · exact forgetfulIndexedCoherent_of_indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj _
      haltingAnchoredNems_forget_coherent
  constructor
  · exact forgetfulAgreementInjects_of_indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj _
      haltingAnchoredNems_forget_injects
  constructor
  · exact nemsFe3IndexedPhantomOps_pullbackAlongDom_align_factors_through_compare_then_host br align
  · exact CertifiedFrontierRepresentation.compareLiftAccountAlong_injective_of_repr_injective
      certifiedFrontierRepresentation_corpus_nems_level1_id certifiedFrontierRepresentation_corpus_nems_level1_id_hasInjectiveCompare

/-!
### **`SPEC_032_HM7_VW2` — tag-witness branch-generic ops (minimal **tag-live** interface)

**Not NEMS:** a **`BranchGenericSemanticTransport`** witness on **`B := TaggedHaltingSummitMasterStaging`** — **`IC () := CorpusStrataCarrier`**, **`indexed` exposes `tag`**, **`agreedSummit` = `tag`**, **`summitReportOf` = identity. Contrasts **`SPEC_032_HM6_QT3`:** NEMS Law X is **`bundle`-only**, so **tag** is invisible there; **here**, **tag** is the **report slot** for **`agreedSummit`**.
-/

/-- **Tag-reading FE-3 slot** at **`B_γ⋆`** (branch-generic, **not** **`haltingAnchoredNems`**). -/
def taggedStaging_tagWitness_branchGeneric_ops (h : HFinalFrameworkWithNEMAnchoredGlue)
    (hF : h.F₀ = haltingFramework) :
    IndexedPhantomCertificateOps Unit (TaggedHaltingSummitMasterStaging h hF) (fun _ : Unit => CorpusStrataCarrier)
      CorpusStrataCarrier where
  indexed := fun _ s => s.tag
  summitReportOf := fun _ t => t
  agreedSummit := fun s => s.tag

theorem taggedStaging_tagWitness_forgetfulIndexedCoherent (h : HFinalFrameworkWithNEMAnchoredGlue)
    (hF : h.F₀ = haltingFramework) :
    ForgetfulIndexedCoherent (taggedStaging_tagWitness_branchGeneric_ops h hF) := fun _ _ => rfl

theorem taggedStaging_tagWitness_forgetfulAgreementInjects (h : HFinalFrameworkWithNEMAnchoredGlue)
    (hF : h.F₀ = haltingFramework) :
    ForgetfulAgreementInjects (taggedStaging_tagWitness_branchGeneric_ops h hF) := by
  intro w_a w_b b1 b2 he
  simpa [taggedStaging_tagWitness_branchGeneric_ops] using he

def taggedStaging_tagWitness_branchGeneric_core (h : HFinalFrameworkWithNEMAnchoredGlue)
    (hF : h.F₀ = haltingFramework) :
    Core Unit (TaggedHaltingSummitMasterStaging h hF) (fun _ : Unit => CorpusStrataCarrier) CorpusStrataCarrier where
  ops := taggedStaging_tagWitness_branchGeneric_ops h hF
  forget_coherent := taggedStaging_tagWitness_forgetfulIndexedCoherent h hF
  forget_injects := taggedStaging_tagWitness_forgetfulAgreementInjects h hF

theorem taggedStaging_tagWitness_agreedSummit_eq_tag (h : HFinalFrameworkWithNEMAnchoredGlue)
    (hF : h.F₀ = haltingFramework) (s : TaggedHaltingSummitMasterStaging h hF) :
    (taggedStaging_tagWitness_branchGeneric_ops h hF).agreedSummit s = s.tag :=
  rfl

/--
  **Tag-distinct staging ⇒ distinct `agreedSummit`** — **HM7** positive content (same **`bundle`**, different **`tag`** still splits this ops).
-/
theorem taggedStaging_tagWitness_agreedSummit_ne_of_tag_ne (h : HFinalFrameworkWithNEMAnchoredGlue)
    (hF : h.F₀ = haltingFramework) (s t : TaggedHaltingSummitMasterStaging h hF) (hne : s.tag ≠ t.tag) :
    (taggedStaging_tagWitness_branchGeneric_ops h hF).agreedSummit s ≠
      (taggedStaging_tagWitness_branchGeneric_ops h hF).agreedSummit t :=
  fun heq => hne (by simpa [taggedStaging_tagWitness_branchGeneric_ops] using heq)

/--
  **HM4 + HM7:** two **`mkStandard`** bundles, different **tags**, **distinguishable** under **tag-witness** ops (**not** under NEMS pullback along **`taggedSummitStaging_toMaster`** — **HM6**).
-/
theorem taggedStaging_tagWitness_agreedSummit_ne_mkStandard_zero_one (h : HFinalFrameworkWithNEMAnchoredGlue)
    (hF : h.F₀ = haltingFramework) :
    (taggedStaging_tagWitness_branchGeneric_ops h hF).agreedSummit ⟨(0 : CorpusStrataCarrier), mkStandard h hF⟩ ≠
      (taggedStaging_tagWitness_branchGeneric_ops h hF).agreedSummit ⟨(1 : CorpusStrataCarrier), mkStandard h hF⟩ :=
  taggedStaging_tagWitness_agreedSummit_ne_of_tag_ne h hF _ _ corpusStrataCarrier_zero_ne_one

end AdequacyArchitecture.Instances
