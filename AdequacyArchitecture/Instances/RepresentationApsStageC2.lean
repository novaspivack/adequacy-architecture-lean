/-
  **SPEC_032 Stage C2 / Phase D — APS parallel of Law X (middle bundle).**

  **NEMS** Law X uses **`proj : B_γ → HaltingAnchoredFaithfulSummitMasterBundle`** (**`RepresentationNemsStageC2`**).
  **APS** theorem-fed FE-3 uses **`RealizationLayer Unit`** as the bundle (**`APSFe2MiddleTransport.apsUnitMiddleIndexedPhantomOps`**).

  This file packages the **same** abstract pattern: an explicit morphism into the **FE-3 bundle type** so
  **`indexedPhantomCertificateOps_pullbackAlongDom proj …`** is meaningful — **`repr`** remains bookkeeping-only.

  **Universe discipline:** middle **`RealizationLayer`** and **`APSFe2MiddleTransport`** spine use **`Type`** (as in that module);
  **`CertifiedFrontierRepresentation`** is instantiated at the same level.

  **v3 note:** **`agreedSummit`** is **`M.ICompIdx : Prop`**; **injective**-**`agreedSummit`** uniqueness (**Phase D v3**) is **not**
  a free theorem on full **`RealizationLayer`** witnesses (distinct layers can share the same proposition).

  **Phase D v5:** **`apsFe3IndexedPhantomOps_pullbackAlongDom_lawX_carrier_bridge`** — same **carrier-bridge** factorization as NEMS,
  via **`apsUnitMiddle_indexedPhantomOps_pullbackAlongDom_comp`**.
-/

import AdequacyArchitecture.Instances.APSFe2MiddleTransport
import AdequacyArchitecture.Portability.SummitRowRepresentation

namespace AdequacyArchitecture.Instances

open AdequacyArchitecture.Portability
open AdequacyArchitecture.Portability.BranchGenericSemanticTransport
open ReflexiveArchitecture.Middle

/--
  **Law X (APS middle) — explicit `proj` into `RealizationLayer Unit`**, dual to **`NemsFe3SummitBundleCompareSection`**.
-/
structure ApsFe3MiddleBundleCompareSection {γ α : Type} (repr : CertifiedFrontierRepresentation γ α)
    (B_γ : Type) where
  proj : B_γ → RealizationLayer Unit

abbrev apsFe3MiddleBundleCompareSection_mk {γ α : Type} {repr : CertifiedFrontierRepresentation γ α}
    {B_γ : Type} (proj : B_γ → RealizationLayer Unit) :
    ApsFe3MiddleBundleCompareSection repr B_γ :=
  { proj := proj }

theorem exists_apsFe3MiddleBundleCompareSection_pullbackAlongDom_iff
    {γ α : Type} (repr : CertifiedFrontierRepresentation γ α) {B_γ : Type}
    (ops' : IndexedPhantomCertificateOps ApsMiddlePhantomTag B_γ (fun _ => Prop) Prop) :
    (∃ σ : ApsFe3MiddleBundleCompareSection repr B_γ,
        ops' = indexedPhantomCertificateOps_pullbackAlongDom σ.proj apsUnitMiddleIndexedPhantomOps) ↔
      (∃ f : B_γ → RealizationLayer Unit,
        ops' = indexedPhantomCertificateOps_pullbackAlongDom f apsUnitMiddleIndexedPhantomOps) := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ.proj, hσ⟩
  · rintro ⟨f, hf⟩
    exact ⟨apsFe3MiddleBundleCompareSection_mk f, hf⟩

def apsFe3MiddleBundleCompareSection_idBundle {γ α : Type}
    (repr : CertifiedFrontierRepresentation γ α) :
    ApsFe3MiddleBundleCompareSection repr (RealizationLayer Unit) where
  proj := fun b : RealizationLayer Unit => b

def apsFe3MiddleBundleCompareSection_precomp {γ α : Type} {repr : CertifiedFrontierRepresentation γ α}
    {B_γ B_δ : Type}
    (σ : ApsFe3MiddleBundleCompareSection repr B_γ)
    (g : B_δ → B_γ) :
    ApsFe3MiddleBundleCompareSection repr B_δ where
  proj := σ.proj ∘ g

theorem nonempty_apsFe3MiddleBundleCompareSection_on_middleBundle {γ α : Type}
    (repr : CertifiedFrontierRepresentation γ α) :
    Nonempty (ApsFe3MiddleBundleCompareSection repr (RealizationLayer Unit)) :=
  ⟨apsFe3MiddleBundleCompareSection_idBundle repr⟩

theorem apsFe3MiddleBundleCompareSection_idBundle_indexedPhantomOps_pullbackAlongDom {γ α : Type}
    (repr : CertifiedFrontierRepresentation γ α) :
    indexedPhantomCertificateOps_pullbackAlongDom (apsFe3MiddleBundleCompareSection_idBundle repr).proj
        apsUnitMiddleIndexedPhantomOps =
      apsUnitMiddleIndexedPhantomOps :=
  apsUnitMiddle_indexedPhantomOps_pullbackAlongDom_id

/--
  **Phase D v5 — carrier bridge** (APS middle). Dual to **`nemsFe3IndexedPhantomOps_pullbackAlongDom_lawX_carrier_bridge`**.
-/
theorem apsFe3IndexedPhantomOps_pullbackAlongDom_lawX_carrier_bridge {γ α : Type}
    {repr : CertifiedFrontierRepresentation γ α} {B_γ : Type}
    (σ : ApsFe3MiddleBundleCompareSection repr B_γ)
    (i : γ → B_γ) :
    indexedPhantomCertificateOps_pullbackAlongDom (σ.proj ∘ i) apsUnitMiddleIndexedPhantomOps =
      indexedPhantomCertificateOps_pullbackAlongDom i
        (indexedPhantomCertificateOps_pullbackAlongDom σ.proj apsUnitMiddleIndexedPhantomOps) :=
  apsUnitMiddle_indexedPhantomOps_pullbackAlongDom_comp σ.proj i

end AdequacyArchitecture.Instances
