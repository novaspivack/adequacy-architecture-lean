/-
  **SPEC_032 — NEMS summit carrier bridge (Working Queue item 1).**

  **Missing datum (machine-named):** representation-side FE-3 on **`γ`** needs **Law X** **`σ.proj : B_γ → MasterBundle`**
  **and** a **carrier map** **`i : γ → B_γ`**; the effective FE-3 precomposition is **`σ.proj ∘ i`** (Phase **D v5**). Compare
  **`repr.π : γ → α`** is **not** this morphism unless a **further** semantic law is added (later phase).

  ## First honest nontrivial **`(B_γ, i, σ)`** — **graph / product staging**

  Given **any** **`b : γ → HaltingAnchoredFaithfulSummitMasterBundle`**, take:

  * **`B_γ := γ × HaltingAnchoredFaithfulSummitMasterBundle`** (staging type **strictly larger** than the host bundle when **`γ`**
    has **>**1 element, e.g. **`Fin 2`** corpus carrier),
  * **`i x := (x, b x)`** (the **graph** of **`b`**),
  * **`σ := nemsFe3SummitBundleCompareSection_mk` `Prod.snd`** (**theorem-backed** Law X — second projection).

  Then **`σ.proj ∘ i = b`** definitionally, so FE-3 on **`γ`** is **`pullbackAlongDom b`**, refactored through the bridge.
  **What makes it possible:** functorial **`indexedPhantomCertificateOps_pullbackAlongDom`** + explicit **Law X** projection; **no**
  **`IsPullbackDisplay`**, **no** **`π`**. **Content:** a **reusable package** (`NemsSummitCarrierBridgeData` + **graph** constructor)
  for any future **`b`** tied to corpus / faithful layers.

  **Forgetful cite (no extra packaging):** same **`br.effectiveProj`**, **`haltingAnchoredNems_forgetful_indexedPhantomOps_pullbackAlongDom br.effectiveProj`**
  (**`NEMSBranchGenericSemanticTransport`**) — the NEMS cert family keeps **stuck `Sort` universe metas** if we abbreviate **`ops`**
  here without a toolchain fix, so we **do not** re-wrap that theorem in this module.

  ## Working Queue item 2 — **declared** compare / bundle triangle

  **`IsPullbackDisplay`** still does **not** produce **`j`**. When **`j : α → HaltingMaster`** is **given** with
  **`∀ x, br.effectiveProj x = j (repr.π x)`**, FE-3 on **`γ`** refactors to **pullback along `π`** **then** pullback along **`j`**
  (**`indexedPhantomCertificateOps_pullbackAlongDom_comp`**). See **`NemsSummitCarrierBridgeCompareAlignment`**.
  **Identity compare:** **`nemsSummitCarrierBridgeCompareAlignment_of_id_compare`** (**`hostBundleMap := effectiveProj`**);
  **prodGraph + id:** **`nemsSummitCarrierBridgeCompareAlignment_prodGraph_of_id_compare`** (**`hostBundleMap := b`**);
  **prodGraph + constant compare** (**`∀ x, repr.π x = c`**): **`nemsSummitCarrierBridgeCompareAlignment_prodGraph_of_constant_compare`**
  (**`hostBundleMap := fun _ => m`** when **`b x = m`**).

  ## Working Queue item 3 — **section-aware** split pack (no megajoin)

  **`nemsSummitSectionAware_pack_isPullback_bridge_v5_forgetfulOnCarrier`** conjoins **`IsPullbackDisplay`** (**RawS1**),
  Phase **D v5** on **`br`**, and **`haltingAnchoredNems_forgetful_indexedPhantomOps_pullbackAlongDom br.effectiveProj`** — four
  **ordered** obligations in one cite. Still **no** bundled **`Sort`** universe join beyond **`γ, α : Type`**.

  ## Concrete **`hostBundleMap`** (**`SPEC_032_HM1`**, **`SPEC_032_HM2_NV`**, **`SPEC_032_HM3_Q7A`**)

  **`nemsHostBundleMap_corpusStrata_mkStandard`** maps every corpus tag to **`mkStandard`** (SPEC_025). Corpus **Level-1** /
  **Level-2 NV** use **`π = id`** and **`prodGraph_of_id_compare`**. **IC CS-3** **`icCs3CertifiedFrontierRepresentation`** uses
  **constant** **`π`** into **`CorpusStrataCarrier`** and **`prodGraph_of_constant_compare`** (**`hostBundleMap`** is the **constant**
  map **`fun _ => mkStandard`**, matching constant graph **`b`**).
-/

import AdequacyArchitecture.Instances.CorpusDischarge
import AdequacyArchitecture.Instances.ICCompareRepresentationPullback
import AdequacyArchitecture.Instances.RepresentationNemsStageC2

namespace AdequacyArchitecture.Instances

open HaltingAnchoredFaithfulSummitMasterBundle
open NemS.Framework
open NemS.Physical
open AdequacyArchitecture
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open AdequacyArchitecture.Portability
open AdequacyArchitecture.Portability.BranchGenericSemanticTransport
open NEMSHaltingAnchoredSemanticReportCertificate

variable {h : HFinalFrameworkWithNEMAnchoredGlue} {hF : h.F₀ = haltingFramework}

abbrev HaltingMaster (h : HFinalFrameworkWithNEMAnchoredGlue) (hF : h.F₀ = haltingFramework) : Type :=
  HaltingAnchoredFaithfulSummitMasterBundle h hF

/--
  **Minimal reusable interface:** carrier **`γ`**, intermediate **`B_γ`**, **Law X** section **`σ`**, bridge **`i`**.
-/
structure NemsSummitCarrierBridgeData
    (h : HFinalFrameworkWithNEMAnchoredGlue) (hF : h.F₀ = haltingFramework)
    {γ α : Type}
    (repr : CertifiedFrontierRepresentation γ α) where
  B_γ : Type
  i : γ → B_γ
  σ : NemsFe3SummitBundleCompareSection h hF repr B_γ

/-- Effective halting-anchored summit map **`γ → MasterBundle`** carried by the bridge. -/
def NemsSummitCarrierBridgeData.effectiveProj
    {γ α : Type} {repr : CertifiedFrontierRepresentation γ α}
    (br : NemsSummitCarrierBridgeData h hF repr) :
    γ → HaltingMaster h hF :=
  br.σ.proj ∘ br.i

/--
  **Carrier bridge ⇒ FE-3 on `γ`:** Phase **D v5** packaged as a single hypothesis (**`NemsSummitCarrierBridgeData`**).
-/
theorem nemsFe3IndexedPhantomOps_carrier_bridge_induces_fe3 {γ α : Type}
    {repr : CertifiedFrontierRepresentation γ α} (br : NemsSummitCarrierBridgeData h hF repr) :
    indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj (@haltingAnchoredNemsIndexedPhantomOps h hF) =
      indexedPhantomCertificateOps_pullbackAlongDom br.i
        (indexedPhantomCertificateOps_pullbackAlongDom br.σ.proj (@haltingAnchoredNemsIndexedPhantomOps h hF)) :=
  nemsFe3IndexedPhantomOps_pullbackAlongDom_lawX_carrier_bridge br.σ br.i

/-!
### Compare / host-bundle triangle (“**`π`** isn’t **`Σ.proj ∘ i`** unless you **say** so”)

**Input:** same **`repr : CertifiedFrontierRepresentation γ α`** as the bridge bookkeeping — **`repr.π : γ → α`** is the Adequacy
compare; **`br.effectiveProj : γ → HaltingMaster`** is the FE-3 carrier. These are **different** morphisms **unless** you supply a
host-side **`hostBundleMap : α → HaltingMaster`** (**semantic lift / section over the host carrier**) and identify the composite.
-/

/--
  **Declared alignment (SPEC_032 Working queue item 2):** host bundle map **`hostBundleMap`** on **`α`** makes **`effectiveProj`**
  factor as **`hostBundleMap ∘ repr.π`**. **No** connection to **`IsPullbackDisplay`** — this is **extra** semantic glue.
-/
structure NemsSummitCarrierBridgeCompareAlignment
    {γ α : Type} {repr : CertifiedFrontierRepresentation γ α}
    (br : NemsSummitCarrierBridgeData h hF repr) where
  hostBundleMap : α → HaltingMaster h hF
  effectiveProj_eq_host_comp_compare : ∀ x : γ, br.effectiveProj x = hostBundleMap (repr.π x)

/--
  **Identity compare (`γ = α`, `repr.π = id`):** set **`hostBundleMap := br.effectiveProj`**. Then **`hostBundleMap ∘ π`**
  equals **`effectiveProj`** (same morphism on **`γ`**).

  Use for **non–prodGraph** bridges where **`b`** is not the primitive input — **`effectiveProj`** is still the semantic map
  **`γ → HaltingMaster`** factored through Law X + **`i`**.
-/
def nemsSummitCarrierBridgeCompareAlignment_of_id_compare {γ : Type}
    {repr : CertifiedFrontierRepresentation γ γ} (hπ : repr.π = id)
    (br : NemsSummitCarrierBridgeData h hF repr) : NemsSummitCarrierBridgeCompareAlignment br where
  hostBundleMap := br.effectiveProj
  effectiveProj_eq_host_comp_compare := fun x =>
    congr_arg br.effectiveProj (congrFun hπ x).symm

/--
  Under **`NemsSummitCarrierBridgeCompareAlignment`**, NEMS FE-3 on **`γ`** is pullback along **`hostBundleMap ∘ repr.π`**.
-/
theorem nemsFe3IndexedPhantomOps_pullbackAlongDom_effectiveProj_eq_of_compare_alignment
    {γ α : Type} {repr : CertifiedFrontierRepresentation γ α}
    (br : NemsSummitCarrierBridgeData h hF repr)
    (align : NemsSummitCarrierBridgeCompareAlignment br) :
    indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj (@haltingAnchoredNemsIndexedPhantomOps h hF) =
      indexedPhantomCertificateOps_pullbackAlongDom (align.hostBundleMap ∘ repr.π)
        (@haltingAnchoredNemsIndexedPhantomOps h hF) :=
  indexedPhantomCertificateOps_pullbackAlongDom_congr_dom (@haltingAnchoredNemsIndexedPhantomOps h hF) fun x => by
    simpa [Function.comp_apply] using align.effectiveProj_eq_host_comp_compare x

/--
  Same hypothesis: FE-3 on **`γ`** equals **pullback along `repr.π`** of **pullback along `hostBundleMap`** — explicit **two-step**
  Adequacy-then-host-bundle pipeline.
-/
theorem nemsFe3IndexedPhantomOps_pullbackAlongDom_align_factors_through_compare_then_host
    {γ α : Type} {repr : CertifiedFrontierRepresentation γ α}
    (br : NemsSummitCarrierBridgeData h hF repr)
    (align : NemsSummitCarrierBridgeCompareAlignment br) :
    indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj (@haltingAnchoredNemsIndexedPhantomOps h hF) =
      indexedPhantomCertificateOps_pullbackAlongDom repr.π
        (indexedPhantomCertificateOps_pullbackAlongDom align.hostBundleMap (@haltingAnchoredNemsIndexedPhantomOps h hF)) := by
  rw [nemsFe3IndexedPhantomOps_pullbackAlongDom_effectiveProj_eq_of_compare_alignment br align]
  rw [haltingAnchoredNems_indexedPhantomOps_pullbackAlongDom_comp align.hostBundleMap repr.π]

/-!
### Graph / **product** bridge (first nontrivial **`B_γ`**) -/

/--
  **Graph constructor:** **`B_γ = γ × MasterBundle`**, **`i`**, graph of **`b`**, **`σ.proj = Prod.snd`**.
-/
def nemsSummitCarrierBridgeData_prodGraph {γ α : Type} (repr : CertifiedFrontierRepresentation γ α)
    (b : γ → HaltingMaster h hF) :
    NemsSummitCarrierBridgeData h hF repr where
  B_γ := γ × HaltingMaster h hF
  i := fun x => (x, b x)
  σ :=
    nemsFe3SummitBundleCompareSection_mk h hF (Prod.snd : γ × HaltingMaster h hF → HaltingMaster h hF)

theorem nemsSummitCarrierBridge_prodGraph_effectiveProj {γ α : Type}
    (repr : CertifiedFrontierRepresentation γ α)
    (b : γ → HaltingMaster h hF) :
    (nemsSummitCarrierBridgeData_prodGraph repr b).effectiveProj = b := by
  funext x
  rfl

theorem nemsFe3IndexedPhantomOps_carrier_prodGraph_eq_pullbackAlongDom_b {γ α : Type}
    (repr : CertifiedFrontierRepresentation γ α)
    (b : γ → HaltingMaster h hF) :
    indexedPhantomCertificateOps_pullbackAlongDom
        (nemsSummitCarrierBridgeData_prodGraph repr b).effectiveProj
        (@haltingAnchoredNemsIndexedPhantomOps h hF) =
      indexedPhantomCertificateOps_pullbackAlongDom b (@haltingAnchoredNemsIndexedPhantomOps h hF) := by
  rw [nemsSummitCarrierBridge_prodGraph_effectiveProj]

/--
  **ProdGraph + identity compare:** **`hostBundleMap := b`** — the **graph law** is **`effectiveProj = b`** on points, and
  **`π = id`** identifies **`b x`** with **`b (π x)`**.

  **Canonical packaging for HM1-style corridors:** **`hostBundleMap`** is **exactly** the morphism **`b`** in
  **`nemsSummitCarrierBridgeData_prodGraph repr b`** (not only a separately named abbrev).
-/
def nemsSummitCarrierBridgeCompareAlignment_prodGraph_of_id_compare {γ : Type}
    {repr : CertifiedFrontierRepresentation γ γ} (hπ : repr.π = id)
    (b : γ → HaltingMaster h hF) :
    NemsSummitCarrierBridgeCompareAlignment (nemsSummitCarrierBridgeData_prodGraph repr b) where
  hostBundleMap := b
  effectiveProj_eq_host_comp_compare := fun x => by
    dsimp [NemsSummitCarrierBridgeData.effectiveProj, nemsSummitCarrierBridgeData_prodGraph]
    rw [show repr.π x = x from by simpa [Function.id_def] using congrFun hπ x]

/--
  **ProdGraph + constant compare:** witness **`c`** with **`∀ x, repr.π x = c`** (e.g. **IC CS-3** corpus compare). Take **`b x = m`**;
  then **`effectiveProj x = b x = m`** on the graph bridge, and **`hostBundleMap := fun _ => m`** matches **`hostBundleMap (repr.π x)`**
  by **β** (the **`_hπ`** hypothesis is the **caller-supplied** constant-**`π`** certificate; it is **not** needed in the **defeq** proof).
-/
def nemsSummitCarrierBridgeCompareAlignment_prodGraph_of_constant_compare
    {γ α : Type} {repr : CertifiedFrontierRepresentation γ α}
    (c : α) (_hπ : ∀ x : γ, repr.π x = c)
    (m : HaltingMaster h hF)
    (b : γ → HaltingMaster h hF)
    (hb : ∀ x : γ, b x = m) :
    NemsSummitCarrierBridgeCompareAlignment (nemsSummitCarrierBridgeData_prodGraph repr b) where
  hostBundleMap := fun _ => m
  effectiveProj_eq_host_comp_compare := fun x => by
    dsimp [NemsSummitCarrierBridgeData.effectiveProj, nemsSummitCarrierBridgeData_prodGraph,
      Function.comp_apply]
    exact hb x

/-!
### Corpus **Fin 2** naming (`CorpusStrataCarrier` = `Fin 2`) -/

/--
  **Corpus-scale graph bridge:** same **`prodGraph`**, **`γ = CorpusStrataCarrier`**.
  Use with any theorem-fed **`b : CorpusStrataCarrier → HaltingMaster`** once that morphism is supplied by a semantic layer.
-/
abbrev nemsSummitCarrierBridgeData_corpusStrataProdGraph
    (repr : CertifiedFrontierRepresentation CorpusStrataCarrier CorpusStrataCarrier)
    (b : CorpusStrataCarrier → HaltingMaster h hF) :
    NemsSummitCarrierBridgeData h hF repr :=
  nemsSummitCarrierBridgeData_prodGraph repr b

/-!
### Working Queue item 3 — **section-aware** parallel pack (**display ∧ bridge ∧ forgetful-on-`γ`**)
-/

/--
  **SPEC_032 — split pack:** **`IsPullbackDisplay`** (𝒞 / RawS1) **∧** carrier-bridge **D v5** **∧** NEMS forgetful on
  **`indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj`**.

  **Honest split:** representation gate and bundle-side FE-3 are **independent** hypotheses; this theorem only **lists** the
  four consequences together for artefacts / proof scripts. **No** **`π`**-to-**`effectiveProj`** identification unless
  **`NemsSummitCarrierBridgeCompareAlignment`** is supplied separately (**`SPEC_032_PI1`**).
-/
theorem nemsSummitSectionAware_pack_isPullback_bridge_v5_forgetfulOnCarrier
    {γ α : Type} {P : AdequacyPredicates γ} {B : BurdenPredicates γ}
    (repr : CertifiedFrontierRepresentation γ α)
    (hdisp : repr.IsPullbackDisplay P B)
    (br : NemsSummitCarrierBridgeData h hF repr) :
    AbsoluteFrontierRawS1 P B ∧
      indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF) =
        indexedPhantomCertificateOps_pullbackAlongDom br.i
          (indexedPhantomCertificateOps_pullbackAlongDom br.σ.proj (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      ForgetfulIndexedCoherent
        (indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      ForgetfulAgreementInjects
        (indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj (@haltingAnchoredNemsIndexedPhantomOps h hF)) := by
  constructor
  · exact absoluteFrontierRawS1_of_valid_certifiedFrontierRepresentation repr hdisp
  constructor
  · exact nemsFe3IndexedPhantomOps_carrier_bridge_induces_fe3 br
  constructor
  · exact forgetfulIndexedCoherent_of_indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj _
      haltingAnchoredNems_forget_coherent
  · exact forgetfulAgreementInjects_of_indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj _
      haltingAnchoredNems_forget_injects

/--
  Same pack **∧** **Stage B** injective **compare-lift** when **`HasInjectiveCompare`**.
-/
theorem nemsSummitSectionAware_pack_isPullback_bridge_v5_forgetfulOnCarrier_injectiveCompareLift
    {γ α : Type} {P : AdequacyPredicates γ} {B : BurdenPredicates γ}
    (repr : CertifiedFrontierRepresentation γ α)
    (hdisp : repr.IsPullbackDisplay P B)
    (hπ : repr.HasInjectiveCompare)
    (br : NemsSummitCarrierBridgeData h hF repr) :
    AbsoluteFrontierRawS1 P B ∧
      indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF) =
        indexedPhantomCertificateOps_pullbackAlongDom br.i
          (indexedPhantomCertificateOps_pullbackAlongDom br.σ.proj (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      ForgetfulIndexedCoherent
        (indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      ForgetfulAgreementInjects
        (indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      Function.Injective (compareLiftAccountAlong repr.π) := by
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
  · exact CertifiedFrontierRepresentation.compareLiftAccountAlong_injective_of_repr_injective repr hπ

/--
  **Pack + `SPEC_032_PI1` triangle:** adjoins the **π-then-host** FE-3 factorization (**equality** of pulled-back ops).
-/
theorem nemsSummitSectionAware_pack_isPullback_bridge_v5_forgetfulOnCarrier_alignCompareFactor
    {γ α : Type} {P : AdequacyPredicates γ} {B : BurdenPredicates γ}
    (repr : CertifiedFrontierRepresentation γ α)
    (hdisp : repr.IsPullbackDisplay P B)
    (br : NemsSummitCarrierBridgeData h hF repr)
    (align : NemsSummitCarrierBridgeCompareAlignment br) :
    AbsoluteFrontierRawS1 P B ∧
      indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF) =
        indexedPhantomCertificateOps_pullbackAlongDom br.i
          (indexedPhantomCertificateOps_pullbackAlongDom br.σ.proj (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      ForgetfulIndexedCoherent
        (indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      ForgetfulAgreementInjects
        (indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj (@haltingAnchoredNemsIndexedPhantomOps h hF) =
        indexedPhantomCertificateOps_pullbackAlongDom repr.π
          (indexedPhantomCertificateOps_pullbackAlongDom align.hostBundleMap (@haltingAnchoredNemsIndexedPhantomOps h hF)) :=
  by
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

/--
  **Full section-aware extension:** align factorization **∧** injective **compare-lift** (**Stage B**).
-/
theorem nemsSummitSectionAware_pack_isPullback_bridge_v5_forgetfulOnCarrier_injectiveCompareLift_alignCompareFactor
    {γ α : Type} {P : AdequacyPredicates γ} {B : BurdenPredicates γ}
    (repr : CertifiedFrontierRepresentation γ α)
    (hdisp : repr.IsPullbackDisplay P B)
    (hπ : repr.HasInjectiveCompare)
    (br : NemsSummitCarrierBridgeData h hF repr)
    (align : NemsSummitCarrierBridgeCompareAlignment br) :
    AbsoluteFrontierRawS1 P B ∧
      indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF) =
        indexedPhantomCertificateOps_pullbackAlongDom br.i
          (indexedPhantomCertificateOps_pullbackAlongDom br.σ.proj (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      ForgetfulIndexedCoherent
        (indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      ForgetfulAgreementInjects
        (indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj (@haltingAnchoredNemsIndexedPhantomOps h hF) =
        indexedPhantomCertificateOps_pullbackAlongDom repr.π
          (indexedPhantomCertificateOps_pullbackAlongDom align.hostBundleMap (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      Function.Injective (compareLiftAccountAlong repr.π) := by
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
  · exact CertifiedFrontierRepresentation.compareLiftAccountAlong_injective_of_repr_injective repr hπ

/-!
### **`SPEC_032_HM1`** — theorem-fed **`hostBundleMap`** (corpus Level-1 id **`π`**, **`mkStandard`**)
-/

/--
  **Host-side semantic map (theorem-fed):** each Adequacy tag on **`CorpusStrataCarrier`** is sent to the **standard** halting
  faithful summit master bundle (**`mkStandard`** — SPEC_025 grid at **`h`**).

  **Semantic content:** unified NEMS summit witness **`h`** (not a varying per-account certificate); **constant** on **`Fin 2`**.
-/
abbrev nemsHostBundleMap_corpusStrata_mkStandard :
    CorpusStrataCarrier → HaltingMaster h hF :=
  fun _ => HaltingAnchoredFaithfulSummitMasterBundle.mkStandard h hF

/--
  Graph bridge for **`certifiedFrontierRepresentation_corpus_nems_level1_id`** with **`b := fun _ => mkStandard`**.
-/
abbrev nemsCorpusLevel1Id_graphBridge_mkStandard :
    NemsSummitCarrierBridgeData h hF certifiedFrontierRepresentation_corpus_nems_level1_id :=
  nemsSummitCarrierBridgeData_corpusStrataProdGraph certifiedFrontierRepresentation_corpus_nems_level1_id
    (fun _ => HaltingAnchoredFaithfulSummitMasterBundle.mkStandard h hF)

/--
  **Alignment** for the corpus id corridor: instance of **`nemsSummitCarrierBridgeCompareAlignment_prodGraph_of_id_compare`**
  (**`hostBundleMap`** is the graph **`b = fun _ => mkStandard`**). Extensionally matches **`nemsHostBundleMap_corpusStrata_mkStandard`**.
-/
def nemsSummitCarrierBridgeCompareAlignment_corpusLevel1Id_graph_mkStandard :
    NemsSummitCarrierBridgeCompareAlignment (@nemsCorpusLevel1Id_graphBridge_mkStandard h hF) :=
  nemsSummitCarrierBridgeCompareAlignment_prodGraph_of_id_compare
    (show certifiedFrontierRepresentation_corpus_nems_level1_id.π = id from rfl)
    (fun _ => HaltingAnchoredFaithfulSummitMasterBundle.mkStandard h hF)

theorem nemsHostBundleMap_corpusStrata_mkStandard_eq_host_of_corpusLevel1_align :
    (@nemsHostBundleMap_corpusStrata_mkStandard h hF) =
      (@nemsSummitCarrierBridgeCompareAlignment_corpusLevel1Id_graph_mkStandard h hF).hostBundleMap :=
  rfl

/--
  **PI1** factorization instantiated (**corpus Level-1 id** + **`mkStandard`** graph bridge).
-/
theorem nemsFe3IndexedPhantomOps_corpusLevel1Id_graph_mkStandard_factors_compare_then_host :
    indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel1Id_graphBridge_mkStandard h hF).effectiveProj
        (@haltingAnchoredNemsIndexedPhantomOps h hF) =
      indexedPhantomCertificateOps_pullbackAlongDom certifiedFrontierRepresentation_corpus_nems_level1_id.π
        (indexedPhantomCertificateOps_pullbackAlongDom (@nemsHostBundleMap_corpusStrata_mkStandard h hF)
          (@haltingAnchoredNemsIndexedPhantomOps h hF)) :=
  nemsFe3IndexedPhantomOps_pullbackAlongDom_align_factors_through_compare_then_host _
    nemsSummitCarrierBridgeCompareAlignment_corpusLevel1Id_graph_mkStandard

/--
  **SA1** aligned pack instantiated: **`IsPullbackDisplay`** for corpus Level-1 **`P,B`** + bridge + **π**/**`hostBundleMap`**
  factorization.
-/
theorem nemsSummitSectionAware_pack_corpusLevel1Id_graph_mkStandard_aligned :
    AbsoluteFrontierRawS1 corpusNemsFin2Adequacy corpusNemsFin2Burden ∧
      indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel1Id_graphBridge_mkStandard h hF).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF) =
        indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel1Id_graphBridge_mkStandard h hF).i
          (indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel1Id_graphBridge_mkStandard h hF).σ.proj
            (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      ForgetfulIndexedCoherent
        (indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel1Id_graphBridge_mkStandard h hF).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      ForgetfulAgreementInjects
        (indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel1Id_graphBridge_mkStandard h hF).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel1Id_graphBridge_mkStandard h hF).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF) =
        indexedPhantomCertificateOps_pullbackAlongDom certifiedFrontierRepresentation_corpus_nems_level1_id.π
          (indexedPhantomCertificateOps_pullbackAlongDom (@nemsHostBundleMap_corpusStrata_mkStandard h hF)
            (@haltingAnchoredNemsIndexedPhantomOps h hF)) := by
  let br := @nemsCorpusLevel1Id_graphBridge_mkStandard h hF
  let align := @nemsSummitCarrierBridgeCompareAlignment_corpusLevel1Id_graph_mkStandard h hF
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

/--
  Same as **`nemsSummitSectionAware_pack_corpusLevel1Id_graph_mkStandard_aligned`**, plus injective **`compareLiftAccountAlong`** (**Stage B**).
-/
theorem nemsSummitSectionAware_pack_corpusLevel1Id_graph_mkStandard_aligned_injectiveCompareLift :
    AbsoluteFrontierRawS1 corpusNemsFin2Adequacy corpusNemsFin2Burden ∧
      indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel1Id_graphBridge_mkStandard h hF).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF) =
        indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel1Id_graphBridge_mkStandard h hF).i
          (indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel1Id_graphBridge_mkStandard h hF).σ.proj
            (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      ForgetfulIndexedCoherent
        (indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel1Id_graphBridge_mkStandard h hF).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      ForgetfulAgreementInjects
        (indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel1Id_graphBridge_mkStandard h hF).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel1Id_graphBridge_mkStandard h hF).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF) =
        indexedPhantomCertificateOps_pullbackAlongDom certifiedFrontierRepresentation_corpus_nems_level1_id.π
          (indexedPhantomCertificateOps_pullbackAlongDom (@nemsHostBundleMap_corpusStrata_mkStandard h hF)
            (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      Function.Injective (compareLiftAccountAlong certifiedFrontierRepresentation_corpus_nems_level1_id.π) := by
  let br := @nemsCorpusLevel1Id_graphBridge_mkStandard h hF
  let align := @nemsSummitCarrierBridgeCompareAlignment_corpusLevel1Id_graph_mkStandard h hF
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
### **`SPEC_032_HM2_NV`** — same **`mkStandard`** graph bridge + alignment for **Level-2 NV** (**IC CS-3 aligned**) id **`repr`**
-/

abbrev nemsCorpusLevel2NvId_graphBridge_mkStandard :
    NemsSummitCarrierBridgeData h hF certifiedFrontierRepresentation_corpus_nems_level2_nv_id :=
  nemsSummitCarrierBridgeData_corpusStrataProdGraph certifiedFrontierRepresentation_corpus_nems_level2_nv_id
    (fun _ => HaltingAnchoredFaithfulSummitMasterBundle.mkStandard h hF)

def nemsSummitCarrierBridgeCompareAlignment_corpusLevel2NvId_graph_mkStandard :
    NemsSummitCarrierBridgeCompareAlignment (@nemsCorpusLevel2NvId_graphBridge_mkStandard h hF) :=
  nemsSummitCarrierBridgeCompareAlignment_prodGraph_of_id_compare
    (show certifiedFrontierRepresentation_corpus_nems_level2_nv_id.π = id from rfl)
    (fun _ => HaltingAnchoredFaithfulSummitMasterBundle.mkStandard h hF)

theorem nemsFe3IndexedPhantomOps_corpusLevel2NvId_graph_mkStandard_factors_compare_then_host :
    indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel2NvId_graphBridge_mkStandard h hF).effectiveProj
        (@haltingAnchoredNemsIndexedPhantomOps h hF) =
      indexedPhantomCertificateOps_pullbackAlongDom certifiedFrontierRepresentation_corpus_nems_level2_nv_id.π
        (indexedPhantomCertificateOps_pullbackAlongDom (@nemsHostBundleMap_corpusStrata_mkStandard h hF)
          (@haltingAnchoredNemsIndexedPhantomOps h hF)) :=
  nemsFe3IndexedPhantomOps_pullbackAlongDom_align_factors_through_compare_then_host _
    nemsSummitCarrierBridgeCompareAlignment_corpusLevel2NvId_graph_mkStandard

theorem nemsSummitSectionAware_pack_corpusLevel2NvId_graph_mkStandard_aligned :
    AbsoluteFrontierRawS1 icCorpusAlignedNonVacuousFinalAdequacy icCorpusAlignedBurden ∧
      indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel2NvId_graphBridge_mkStandard h hF).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF) =
        indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel2NvId_graphBridge_mkStandard h hF).i
          (indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel2NvId_graphBridge_mkStandard h hF).σ.proj
            (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      ForgetfulIndexedCoherent
        (indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel2NvId_graphBridge_mkStandard h hF).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      ForgetfulAgreementInjects
        (indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel2NvId_graphBridge_mkStandard h hF).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel2NvId_graphBridge_mkStandard h hF).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF) =
        indexedPhantomCertificateOps_pullbackAlongDom certifiedFrontierRepresentation_corpus_nems_level2_nv_id.π
          (indexedPhantomCertificateOps_pullbackAlongDom (@nemsHostBundleMap_corpusStrata_mkStandard h hF)
            (@haltingAnchoredNemsIndexedPhantomOps h hF)) := by
  let br := @nemsCorpusLevel2NvId_graphBridge_mkStandard h hF
  let align := @nemsSummitCarrierBridgeCompareAlignment_corpusLevel2NvId_graph_mkStandard h hF
  constructor
  · exact absoluteFrontierRawS1_of_valid_certifiedFrontierRepresentation
      certifiedFrontierRepresentation_corpus_nems_level2_nv_id
      certifiedFrontierRepresentation_corpus_nems_level2_nv_id_isPullbackDisplay
  constructor
  · exact nemsFe3IndexedPhantomOps_carrier_bridge_induces_fe3 br
  constructor
  · exact forgetfulIndexedCoherent_of_indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj _
      haltingAnchoredNems_forget_coherent
  constructor
  · exact forgetfulAgreementInjects_of_indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj _
      haltingAnchoredNems_forget_injects
  · exact nemsFe3IndexedPhantomOps_pullbackAlongDom_align_factors_through_compare_then_host br align

theorem nemsSummitSectionAware_pack_corpusLevel2NvId_graph_mkStandard_aligned_injectiveCompareLift :
    AbsoluteFrontierRawS1 icCorpusAlignedNonVacuousFinalAdequacy icCorpusAlignedBurden ∧
      indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel2NvId_graphBridge_mkStandard h hF).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF) =
        indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel2NvId_graphBridge_mkStandard h hF).i
          (indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel2NvId_graphBridge_mkStandard h hF).σ.proj
            (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      ForgetfulIndexedCoherent
        (indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel2NvId_graphBridge_mkStandard h hF).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      ForgetfulAgreementInjects
        (indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel2NvId_graphBridge_mkStandard h hF).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      indexedPhantomCertificateOps_pullbackAlongDom (@nemsCorpusLevel2NvId_graphBridge_mkStandard h hF).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF) =
        indexedPhantomCertificateOps_pullbackAlongDom certifiedFrontierRepresentation_corpus_nems_level2_nv_id.π
          (indexedPhantomCertificateOps_pullbackAlongDom (@nemsHostBundleMap_corpusStrata_mkStandard h hF)
            (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      Function.Injective (compareLiftAccountAlong certifiedFrontierRepresentation_corpus_nems_level2_nv_id.π) := by
  let br := @nemsCorpusLevel2NvId_graphBridge_mkStandard h hF
  let align := @nemsSummitCarrierBridgeCompareAlignment_corpusLevel2NvId_graph_mkStandard h hF
  constructor
  · exact absoluteFrontierRawS1_of_valid_certifiedFrontierRepresentation
      certifiedFrontierRepresentation_corpus_nems_level2_nv_id
      certifiedFrontierRepresentation_corpus_nems_level2_nv_id_isPullbackDisplay
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
      certifiedFrontierRepresentation_corpus_nems_level2_nv_id
      certifiedFrontierRepresentation_corpus_nems_level2_nv_id_hasInjectiveCompare

/-!
### **`SPEC_032_HM3_Q7A`** — **IC CS-3** constant compare **`π`**, same **`mkStandard`** graph (no injective compare-lift)

**`icCs3CertifiedFrontierRepresentation`:** **`γ = icNemsSpineCompressionCarrier`**, **`α = CorpusStrataCarrier`**, **`π`** constant.
**Compare-lift injectivity** fails — see **`icCs3CertifiedFrontierRepresentation_not_injectiveCompare`**; only the **aligned** (non-injective) **SA1** line is given.
-/

abbrev nemsIcCs3_graphBridge_mkStandard :
    NemsSummitCarrierBridgeData h hF icCs3CertifiedFrontierRepresentation :=
  nemsSummitCarrierBridgeData_prodGraph icCs3CertifiedFrontierRepresentation
    (fun _ => HaltingAnchoredFaithfulSummitMasterBundle.mkStandard h hF)

def nemsSummitCarrierBridgeCompareAlignment_icCs3_graph_mkStandard :
    NemsSummitCarrierBridgeCompareAlignment (@nemsIcCs3_graphBridge_mkStandard h hF) :=
  nemsSummitCarrierBridgeCompareAlignment_prodGraph_of_constant_compare
    (⟨0, by decide⟩ : CorpusStrataCarrier)
    (fun _ =>
      show icCs3CertifiedFrontierRepresentation.π _ = ⟨0, by decide⟩ from rfl)
    (HaltingAnchoredFaithfulSummitMasterBundle.mkStandard h hF)
    (fun _ => HaltingAnchoredFaithfulSummitMasterBundle.mkStandard h hF)
    (fun _ => rfl)

theorem nemsFe3IndexedPhantomOps_icCs3_graph_mkStandard_factors_compare_then_host :
    indexedPhantomCertificateOps_pullbackAlongDom (@nemsIcCs3_graphBridge_mkStandard h hF).effectiveProj
        (@haltingAnchoredNemsIndexedPhantomOps h hF) =
      indexedPhantomCertificateOps_pullbackAlongDom icCs3CertifiedFrontierRepresentation.π
        (indexedPhantomCertificateOps_pullbackAlongDom (@nemsHostBundleMap_corpusStrata_mkStandard h hF)
          (@haltingAnchoredNemsIndexedPhantomOps h hF)) :=
  nemsFe3IndexedPhantomOps_pullbackAlongDom_align_factors_through_compare_then_host _
    nemsSummitCarrierBridgeCompareAlignment_icCs3_graph_mkStandard

theorem nemsSummitSectionAware_pack_icCs3_graph_mkStandard_aligned :
    AbsoluteFrontierRawS1 icNativeCompressionLawfulArchitecture_cs3_pullback.P
      icNativeCompressionLawfulArchitecture_cs3_pullback.B ∧
      indexedPhantomCertificateOps_pullbackAlongDom (@nemsIcCs3_graphBridge_mkStandard h hF).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF) =
        indexedPhantomCertificateOps_pullbackAlongDom (@nemsIcCs3_graphBridge_mkStandard h hF).i
          (indexedPhantomCertificateOps_pullbackAlongDom (@nemsIcCs3_graphBridge_mkStandard h hF).σ.proj
            (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      ForgetfulIndexedCoherent
        (indexedPhantomCertificateOps_pullbackAlongDom (@nemsIcCs3_graphBridge_mkStandard h hF).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      ForgetfulAgreementInjects
        (indexedPhantomCertificateOps_pullbackAlongDom (@nemsIcCs3_graphBridge_mkStandard h hF).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      indexedPhantomCertificateOps_pullbackAlongDom (@nemsIcCs3_graphBridge_mkStandard h hF).effectiveProj
          (@haltingAnchoredNemsIndexedPhantomOps h hF) =
        indexedPhantomCertificateOps_pullbackAlongDom icCs3CertifiedFrontierRepresentation.π
          (indexedPhantomCertificateOps_pullbackAlongDom (@nemsHostBundleMap_corpusStrata_mkStandard h hF)
            (@haltingAnchoredNemsIndexedPhantomOps h hF)) := by
  let br := @nemsIcCs3_graphBridge_mkStandard h hF
  let align := @nemsSummitCarrierBridgeCompareAlignment_icCs3_graph_mkStandard h hF
  constructor
  · exact absoluteFrontierRawS1_of_valid_certifiedFrontierRepresentation icCs3CertifiedFrontierRepresentation
      icCs3CertifiedFrontierRepresentation_isPullbackDisplay
  constructor
  · exact nemsFe3IndexedPhantomOps_carrier_bridge_induces_fe3 br
  constructor
  · exact forgetfulIndexedCoherent_of_indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj _
      haltingAnchoredNems_forget_coherent
  constructor
  · exact forgetfulAgreementInjects_of_indexedPhantomCertificateOps_pullbackAlongDom br.effectiveProj _
      haltingAnchoredNems_forget_injects
  · exact nemsFe3IndexedPhantomOps_pullbackAlongDom_align_factors_through_compare_then_host br align

end AdequacyArchitecture.Instances
