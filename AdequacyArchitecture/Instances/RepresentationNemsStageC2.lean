/-
  **SPEC_032 Stage C2 — NEMS injective-first: FE-3 / representation composition boundary.**

  ## Positive (machine-checked elsewhere)

  * **`Portability/BranchGenericSemanticTransport`:** functorial **`indexedPhantomCertificateOps_pullbackAlongDom`**,
    **`core_pullbackAlongDom`**, **`phantomReindexLayer_pullbackAlongDom`**, with forgetful lemmas preserved.
  * **`NEMSBranchGenericSemanticTransport`:** NEMS instantiations —
    **`haltingAnchoredNems_forgetful_indexedPhantomOps_pullbackAlongDom`**,
    **`haltingAnchoredNems_phantomReindex_pullbackAlongDom`**,
    **`haltingAnchoredNems_nonempty_phantomReindex_pullbackAlongDom`**.

  **Composition recipe (semantic transport after representation pullback).** Given **`repr`**, **`IsPullbackDisplay`**, and
  injective compare (**Stage B**), you have **`AbsoluteFrontierRawS1`** on **`γ`**. Given **Law X** **`σ`** below, instantiate
  **`haltingAnchoredNems_forgetful_indexedPhantomOps_pullbackAlongDom σ.proj`** for pulled-back forgetful FE-3 on **`B_γ`**,
  and **`haltingAnchoredNems_phantomReindex_pullbackAlongDom σ.proj`** / **`haltingAnchoredNems_nonempty_phantomReindex_pullbackAlongDom σ.proj`**
  for reindex. **Stage C v1** **`repr_pullback_pack_absoluteFrontier_nems_fe3_forgetful_injective_compareLift`** packages RawS1 +
  *host-side* NEMS forgetful laws **without** **`σ`**; replacing the host-side half with the pulled-back instance is exactly
  this recipe.

  ## Named obstruction — **Law X: `NemsFe3SummitBundleCompareSection`**

  **`HasInjectiveCompare`** does **not** define **`σ.proj`**. Compare **`π : γ → α`** acts on **Adequacy carriers**; NEMS FE-3
  **`indexed`** takes **`HaltingAnchoredFaithfulSummitMasterBundle`**. Without an explicit morphism
  **`B_γ → HaltingAnchoredFaithfulSummitMasterBundle`**, there is **no** canonical **`B_γ`-typed** pullback of
  **`haltingAnchoredNemsIndexedPhantomOps`**. **`IsPullbackDisplay`** yields **`LawfulAdequacyArchitecture γ`** — not that
  morphism.

  **Lean elaboration note:** packing **`CertifiedFrontierRepresentation`**, **`AbsoluteFrontierRawS1`**, and the full
  **`NEMSHaltingAnchoredSemanticReportCertificate`** spine in **one** theorem leaves **unsolved `Sort` universe**
  metavariables in this toolchain; the **split** lemmas above are the stable cites. This file **names** Law X and **records**
  the honest composition pattern.

  **SPEC_032 Phase D (v2):** **`exists_indexedPhantomCertificateOps_pullbackAlongDom_iff`**
  / **`exists_haltingAnchoredNems_indexedPhantomOps_pullbackAlongDom_iff`** — FE-3 pullback along **`f`** **iff**
  **`summitReportOf`**, **`indexed`**, **`agreedSummit`** agree with host via **that same **`f`**; Law X **`proj`** is that
  witness ( **`nemsFe3SummitBundleCompareSection_mk`** ).   **API note:** **`IndexedPhantomCertificateOps.summitReportOf`** is
  **`∀ w, IC w → R`** (explicit tag **`w`**) for clean extensionality.

  **SPEC_032 Phase D (v3):** when **`agreed_summit`** is **injective** on **`HaltingAnchoredFaithfulSummitMasterBundle`**, **equal**
  pulled-back NEMS ops force **equal** Law X **`proj`**
  (**`nemsFe3SummitBundleCompareSection_eq_of_pullback_ops_eq_of_agreed_summit_injective`**); underlying FE-3:
  **`indexedPhantomCertificateOps_pullbackAlongDom_f_{eq_of_agreedSummit_injective, unique_of_eq_pullbacks}`** /
  **`haltingAnchoredNems_indexedPhantomOps_pullbackAlongDom_f_*`**.

  **SPEC_032 Phase D (v5):** **`nemsFe3IndexedPhantomOps_pullbackAlongDom_lawX_carrier_bridge`** — for **extra** **`i : γ → B_γ`**
  (not **`repr.π`**), NEMS FE-3 on **`γ`** is **`pullbackAlongDom (σ.proj ∘ i)`**, equal to **two-stage** pullback (**Law X** then **`i`**).
  **Elaboration:** stated at **`γ, α, B_γ : Type`** so **`B_γ`** matches the NEMS FE-3 bundle slot (same level as host **`haltingAnchoredNemsIndexedPhantomOps`**); higher-universe carriers re-use the pattern via **`ULift`** or a localized copy if needed.
  **`IsPullbackDisplay`** still does **not** supply **`i`** or **`σ`**.
  **Concrete bridge (Working queue item 1):** **`Instances/NemsSummitCarrierBridge`** — **`NemsSummitCarrierBridgeData`**, **`nemsSummitCarrierBridgeData_prodGraph`** (graph / product **`(B_γ, i, σ)`**), **`nemsFe3IndexedPhantomOps_carrier_bridge_induces_fe3`**; note **`SPEC_032_CB1`**.
  **Compare triangle (Working queue item 2):** **`NemsSummitCarrierBridgeCompareAlignment`**, **`nemsFe3IndexedPhantomOps_pullbackAlongDom_align_factors_through_compare_then_host`**; note **`SPEC_032_PI1`**.
  **Section-aware pack (Working queue item 3):** **`nemsSummitSectionAware_pack_isPullback_bridge_v5_forgetfulOnCarrier`** (+ variants); note **`SPEC_032_SA1`**.

  **SPEC_032 Phase D (v1, this file):** **`nemsFe3SummitBundleCompareSection_idBundle`** (canonical **`proj := id`**) proves Law X is
  **always satisfiable** once **`B_γ`** is taken to be the **host** master-bundle type; **`nemsFe3SummitBundleCompareSection_precomp`**
  packages **`proj := σ.proj ∘ g`**, matching **`indexedPhantomCertificateOps_pullbackAlongDom_comp`** / NEMS
  **`haltingAnchoredNems_indexedPhantomOps_pullbackAlongDom_comp`**. Substantive Law X content is **aligning** **`B_γ`** with native
  **`γ`** data — not raw **nonemptiness**. See epic § Phase D for necessity / nontrivial instances / obstructions.

  **Scope.** NEMS (not IC/APS) for this Stage C2 outcome.
-/

import AdequacyArchitecture.Instances.NEMSBranchGenericSemanticTransport
import AdequacyArchitecture.Portability.SummitRowRepresentation

namespace AdequacyArchitecture.Instances

open HaltingAnchoredFaithfulSummitMasterBundle
open NemS.Framework
open NemS.MFRR
open NemS.Physical
open AdequacyArchitecture.Portability
open AdequacyArchitecture.Portability.BranchGenericSemanticTransport
open NEMSHaltingAnchoredSemanticReportCertificate

universe u

/--
  **Law X — `NemsFe3SummitBundleCompareSection`:** explicit **`proj : B_γ → HaltingAnchoredFaithfulSummitMasterBundle`**.

  Parameters **`h`**, **`hF`** fix the halting-anchored summit corridor. **`repr`** bookkeeps the intended representation
  context; **`proj`** does **not** mention Adequacy **`repr.π`**.
-/
structure NemsFe3SummitBundleCompareSection
    (h : HFinalFrameworkWithNEMAnchoredGlue) (hF : h.F₀ = haltingFramework)
    {γ α : Type u}
    (repr : CertifiedFrontierRepresentation γ α) (B_γ : Type) where
  proj : B_γ → HaltingAnchoredFaithfulSummitMasterBundle h hF

/--
  **Phase D:** package **`proj`** as Law X (**`repr`** is bookkeeping-only for this morphism).
-/
abbrev nemsFe3SummitBundleCompareSection_mk
    (h : HFinalFrameworkWithNEMAnchoredGlue) (hF : h.F₀ = haltingFramework)
    {γ α : Type u} {repr : CertifiedFrontierRepresentation γ α} {B_γ : Type}
    (proj : B_γ → HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    NemsFe3SummitBundleCompareSection h hF repr B_γ :=
  { proj := proj }

/--
  **Phase D:** ∃ Law X **`σ`** with **`ops' = pullback σ.proj nems`** **iff** ∃ bare **`f`** with the same pullback — the
  structure is **only** **`proj`**.
-/
theorem exists_nemsFe3SummitBundleCompareSection_pullbackAlongDom_iff
    {h : HFinalFrameworkWithNEMAnchoredGlue} {hF : h.F₀ = haltingFramework}
    {γ α : Type u} (repr : CertifiedFrontierRepresentation γ α) {B_γ : Type}
    (ops' :
      IndexedPhantomCertificateOps
        NemsPhantomOuterTag B_γ
        (fun _ω =>
          NEMSHaltingAnchoredSemanticReportCertificate h hF
            (diagonal_barrier_rt haltingFramework (dc := haltingFramework_diagonalCapable)))
        (HaltingAnchoredGluedSummitSemanticReport h hF)) :
    (∃ σ : NemsFe3SummitBundleCompareSection h hF repr B_γ,
        ops' =
          indexedPhantomCertificateOps_pullbackAlongDom σ.proj (@haltingAnchoredNemsIndexedPhantomOps h hF)) ↔
      (∃ f : B_γ → HaltingAnchoredFaithfulSummitMasterBundle h hF,
        ops' =
          indexedPhantomCertificateOps_pullbackAlongDom f (@haltingAnchoredNemsIndexedPhantomOps h hF)) := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ.proj, hσ⟩
  · rintro ⟨f, hf⟩
    exact ⟨nemsFe3SummitBundleCompareSection_mk h hF f, hf⟩

/--
  **Phase D v3 (conditional):** same **pulled-back** NEMS ops ⇒ **same** Law X **`proj`**, if **`agreed_summit`** is
  **injective** on the master bundle (**`haltingAnchoredNems_indexedPhantomOps_pullbackAlongDom_f_unique_of_eq_pullbacks`**).
-/
theorem nemsFe3SummitBundleCompareSection_eq_of_pullback_ops_eq_of_agreed_summit_injective
    {h : HFinalFrameworkWithNEMAnchoredGlue} {hF : h.F₀ = haltingFramework}
    {γ α : Type u} {repr : CertifiedFrontierRepresentation γ α} {B_γ : Type}
    (h_inj :
      ∀ b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF,
        agreed_summit b₁ = agreed_summit b₂ → b₁ = b₂)
    (σ τ : NemsFe3SummitBundleCompareSection h hF repr B_γ)
    (h_eq :
      indexedPhantomCertificateOps_pullbackAlongDom σ.proj (@haltingAnchoredNemsIndexedPhantomOps h hF) =
        indexedPhantomCertificateOps_pullbackAlongDom τ.proj (@haltingAnchoredNemsIndexedPhantomOps h hF)) :
    σ = τ := by
  rcases σ with ⟨p⟩
  rcases τ with ⟨q⟩
  have hpq : p = q :=
    haltingAnchoredNems_indexedPhantomOps_pullbackAlongDom_f_eq_of_agreed_summit_injective h_inj p q h_eq
  rw [hpq]

/--
  **Phase D — canonical Law X:** use the **master bundle** as **`B_γ`** and **`proj := id`**.

  This is the **identity section** for bundle-side FE-3 pullback: **`haltingAnchoredNems_indexedPhantomOps_pullbackAlongDom_id`**.
-/
def nemsFe3SummitBundleCompareSection_idBundle
    (h : HFinalFrameworkWithNEMAnchoredGlue) (hF : h.F₀ = haltingFramework)
    {γ α : Type u}
    (repr : CertifiedFrontierRepresentation γ α) :
    NemsFe3SummitBundleCompareSection h hF repr (HaltingAnchoredFaithfulSummitMasterBundle h hF) where
  proj := id

/--
  **Phase D — precomposition:** if **`σ`** is Law X on **`B_γ`** and **`g : B_δ → B_γ`**, then **`proj := σ.proj ∘ g`**
  is Law X on **`B_δ`**, and NEMS FE-3 pullback **composes** accordingly
  (**`haltingAnchoredNems_indexedPhantomOps_pullbackAlongDom_comp`**).
-/
def nemsFe3SummitBundleCompareSection_precomp
    {h : HFinalFrameworkWithNEMAnchoredGlue} {hF : h.F₀ = haltingFramework}
    {γ α : Type u} {repr : CertifiedFrontierRepresentation γ α}
    {B_γ B_δ : Type}
    (σ : NemsFe3SummitBundleCompareSection h hF repr B_γ)
    (g : B_δ → B_γ) :
    NemsFe3SummitBundleCompareSection h hF repr B_δ where
  proj := σ.proj ∘ g

theorem nonempty_nemsFe3SummitBundleCompareSection_on_masterBundle
    (h : HFinalFrameworkWithNEMAnchoredGlue) (hF : h.F₀ = haltingFramework)
    {γ α : Type u} (repr : CertifiedFrontierRepresentation γ α) :
    Nonempty (NemsFe3SummitBundleCompareSection h hF repr (HaltingAnchoredFaithfulSummitMasterBundle h hF)) :=
  ⟨nemsFe3SummitBundleCompareSection_idBundle h hF repr⟩

/--
  **Phase D (positive anchor):** the **canonical** Law X choice **`proj := id`** induces the **identity** FE-3 pullback on
  host NEMS ops — so this Law X instance is the **neutral** element for **`indexedPhantomCertificateOps_pullbackAlongDom`**.
-/
theorem nemsFe3SummitBundleCompareSection_idBundle_indexedPhantomOps_pullbackAlongDom
    (h : HFinalFrameworkWithNEMAnchoredGlue) (hF : h.F₀ = haltingFramework)
    {γ α : Type u} (repr : CertifiedFrontierRepresentation γ α) :
    indexedPhantomCertificateOps_pullbackAlongDom (nemsFe3SummitBundleCompareSection_idBundle h hF repr).proj
        (@haltingAnchoredNemsIndexedPhantomOps h hF) =
      @haltingAnchoredNemsIndexedPhantomOps h hF :=
  haltingAnchoredNems_indexedPhantomOps_pullbackAlongDom_id

/--
  **Phase D v5 — carrier bridge.** Given Law X **`σ`** on **`B_γ`**, any choice of **`i : γ → B_γ`** yields NEMS FE-3 on **`γ`**
  by **`proj := σ.proj ∘ i`**. This **agrees** with **pulling back first along **`σ.proj`** (to **`B_γ`**) **then** along **`i`**
  — functoriality (**`indexedPhantomCertificateOps_pullbackAlongDom_comp`**).

  **Scope note:** **`repr.π : γ → α`** compares **Adequacy** strata; it is **a different morphism species** unless a **further**
  semantic identification **`B_γ`** / master-bundle data with those carriers is **added by hand** (not from **`IsPullbackDisplay`**).

  **Universe note:** **`γ, α : Type`** (not **`Type u`**) so **`indexedPhantomCertificateOps_pullbackAlongDom_comp`** agrees with the NEMS
  host ops bundle universe (**`B_γ : Type`**).
-/
theorem nemsFe3IndexedPhantomOps_pullbackAlongDom_lawX_carrier_bridge
    {h : HFinalFrameworkWithNEMAnchoredGlue} {hF : h.F₀ = haltingFramework}
    {γ α : Type} {repr : CertifiedFrontierRepresentation γ α} {B_γ : Type}
    (σ : NemsFe3SummitBundleCompareSection h hF repr B_γ)
    (i : γ → B_γ) :
    indexedPhantomCertificateOps_pullbackAlongDom (σ.proj ∘ i) (@haltingAnchoredNemsIndexedPhantomOps h hF) =
      indexedPhantomCertificateOps_pullbackAlongDom i
        (indexedPhantomCertificateOps_pullbackAlongDom σ.proj (@haltingAnchoredNemsIndexedPhantomOps h hF)) :=
  indexedPhantomCertificateOps_pullbackAlongDom_comp (@haltingAnchoredNemsIndexedPhantomOps h hF) σ.proj i

end AdequacyArchitecture.Instances
