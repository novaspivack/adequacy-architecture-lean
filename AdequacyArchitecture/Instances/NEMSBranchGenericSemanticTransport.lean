/-
  **SPEC_029_FR1 — FE-3:** the halting-anchored **NEMS** semantic summit stack as an instance of
  **`Portability.BranchGenericSemanticTransport`**.

  **Singleton phantom index (elaboration hygiene).** Phase **E** **`SemanticRemainder PUnit`** used as the **family
  `IC w`** inside a **`def`** that still quantifies **`{h hF}`** can leave **stuck `max u₁ u₂`** metavariables. Here
  **`W := Unit`**: a typed slot for **FE-3 / FE-2** transport without importing multi-tag grid data on-spine.
  **Certificate types** use **`diagonal_barrier_rt haltingFramework (dc := haltingFramework_diagonalCapable)`** —
  **defeq** to **`faithful_nems_semantic_remainder_at_unit`** / EPIC_018 — so this layer does not mention the
  polymorphic remainder theorem constant at **`def`** sites. Multi-tag / `PLift` outer proofs stay **off-spine** per
  **SPEC_025** transport; **`summitTracked`** remains phantom in the branch.

  **Branch-specific.** `(h, hF)`, **`HaltingAnchoredFaithfulSummitMasterBundle`**, **Phase D** shape, halting anchor data.

  **Reusable (via `BranchGenericSemanticTransport`).** **`IndexedPhantomCertificateOps`**, **`Core`**, **`PhantomReindexLayer`**
  with inlined **`⟨b.summitCert.summitTracked⟩`** (no **`indexed_certificate`** constant in the **`def`** spine).

  **Companion facts.** **`as_fourfold_core`**, **`NemsRemainderConcrete`** — cite separately (**SPEC_025_YG2**).
-/

import AdequacyArchitecture.Instances.NEMSSemanticFaithfulTransport
import AdequacyArchitecture.Portability.BranchGenericSemanticTransport
import Mathlib.Tactic
import NemS.MFRR.DiagonalBarrier

namespace AdequacyArchitecture.Instances

open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Portability.BranchGenericSemanticTransport
open ReflexiveArchitecture.Instances
open HaltingAnchoredFaithfulSummitMasterBundle
open NEMSHaltingAnchoredSemanticReportCertificate
open NEMSSemanticFaithfulTransport
open NemS.Framework
open NemS
open NemS.MFRR
open NemS.Physical

/-- **EPIC_018** remainder at `()`, **concrete** spelling (for notes / links — not the spine of **`W`** here). -/
abbrev NemsRemainderConcrete : Prop :=
  ¬ ComputablePred haltingFramework_diagonalCapable.asr.RT

/-- **`FE-3` phantom slot** — **singleton** so **`IC : W → Sort`** elaborates cleanly in **`def`** spines (see module doc). -/
abbrev NemsPhantomOuterTag : Type :=
  Unit

/-- Inline **`diagonal_barrier_rt haltingFramework`** in certificate **types** (defeq to
    **`faithful_nems_semantic_remainder_at_unit`**) so this spine does not reference the polymorphic theorem
    constant at **`def`** sites. -/
def haltingAnchoredNemsIndexedPhantomOps
    {h : HFinalFrameworkWithNEMAnchoredGlue} {hF : h.F₀ = haltingFramework} :
    IndexedPhantomCertificateOps
      NemsPhantomOuterTag
      (HaltingAnchoredFaithfulSummitMasterBundle h hF)
      (fun _ω =>
        NEMSHaltingAnchoredSemanticReportCertificate h hF
          (diagonal_barrier_rt haltingFramework (dc := haltingFramework_diagonalCapable)))
      (HaltingAnchoredGluedSummitSemanticReport h hF) where
  indexed := fun _ω b =>
    (⟨b.summitCert.summitTracked⟩ :
      NEMSHaltingAnchoredSemanticReportCertificate h hF
        (diagonal_barrier_rt haltingFramework (dc := haltingFramework_diagonalCapable)))
  summitReportOf := fun _w c => c.summitTracked
  agreedSummit := agreed_summit

theorem haltingAnchoredNems_indexed_eq_indexed_certificate
    {h : HFinalFrameworkWithNEMAnchoredGlue} {hF : h.F₀ = haltingFramework}
    (ω : NemsPhantomOuterTag) (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    (@haltingAnchoredNemsIndexedPhantomOps h hF).indexed ω b =
      indexed_certificate
        (diagonal_barrier_rt haltingFramework (dc := haltingFramework_diagonalCapable)) b :=
  rfl

theorem haltingAnchoredNems_forget_coherent
    {h : HFinalFrameworkWithNEMAnchoredGlue} {hF : h.F₀ = haltingFramework} :
    ForgetfulIndexedCoherent (@haltingAnchoredNemsIndexedPhantomOps h hF) := by
  intro _ω b
  rfl

theorem haltingAnchoredNems_forget_injects
    {h : HFinalFrameworkWithNEMAnchoredGlue} {hF : h.F₀ = haltingFramework} :
    ForgetfulAgreementInjects (@haltingAnchoredNemsIndexedPhantomOps h hF) :=
  fun _ _ _ _ hsr => hsr

def haltingAnchoredNemsBranchGenericCore
    {h : HFinalFrameworkWithNEMAnchoredGlue} {hF : h.F₀ = haltingFramework} :
    Core
      NemsPhantomOuterTag
      (HaltingAnchoredFaithfulSummitMasterBundle h hF)
      (fun _ω =>
        NEMSHaltingAnchoredSemanticReportCertificate h hF
          (diagonal_barrier_rt haltingFramework (dc := haltingFramework_diagonalCapable)))
      (HaltingAnchoredGluedSummitSemanticReport h hF) where
  ops := haltingAnchoredNemsIndexedPhantomOps
  forget_coherent := haltingAnchoredNems_forget_coherent
  forget_injects := haltingAnchoredNems_forget_injects

def haltingAnchoredNemsPhantomReindexLayer
    {h : HFinalFrameworkWithNEMAnchoredGlue} {hF : h.F₀ = haltingFramework} :
    PhantomReindexLayer
      NemsPhantomOuterTag
      (HaltingAnchoredFaithfulSummitMasterBundle h hF)
      (fun _ω =>
        NEMSHaltingAnchoredSemanticReportCertificate h hF
          (diagonal_barrier_rt haltingFramework (dc := haltingFramework_diagonalCapable)))
      (HaltingAnchoredGluedSummitSemanticReport h hF)
      (@haltingAnchoredNemsIndexedPhantomOps h hF) where
  reindex := fun {_ _} _ c =>
    (⟨c.summitTracked⟩ :
      NEMSHaltingAnchoredSemanticReportCertificate h hF
        (diagonal_barrier_rt haltingFramework (dc := haltingFramework_diagonalCapable)))
  forget_reindex := fun {_ _} _ _ => rfl

/--
  **SPEC_032 Stage C2:** NEMS forgetful discipline for **bundle-side** pullback of
  **`haltingAnchoredNemsIndexedPhantomOps`** along any **`f : B' → HaltingAnchoredFaithfulSummitMasterBundle`**.

  Proved in this module (not beside **`CertifiedFrontierRepresentation`**) so **`NEMSHaltingAnchoredSemanticReportCertificate`**
  universe parameters elaborate once.
-/
theorem haltingAnchoredNems_forgetful_indexedPhantomOps_pullbackAlongDom
    {h : HFinalFrameworkWithNEMAnchoredGlue} {hF : h.F₀ = haltingFramework}
    {B' : Type}
    (f : B' → HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    ForgetfulIndexedCoherent
      (indexedPhantomCertificateOps_pullbackAlongDom f (@haltingAnchoredNemsIndexedPhantomOps h hF)) ∧
      ForgetfulAgreementInjects
        (indexedPhantomCertificateOps_pullbackAlongDom f (@haltingAnchoredNemsIndexedPhantomOps h hF)) := by
  refine And.intro ?_ ?_
  · exact forgetfulIndexedCoherent_of_indexedPhantomCertificateOps_pullbackAlongDom f _
      haltingAnchoredNems_forget_coherent
  · exact forgetfulAgreementInjects_of_indexedPhantomCertificateOps_pullbackAlongDom f _
      haltingAnchoredNems_forget_injects

/--
  **SPEC_032 Phase D:** pulling NEMS FE-3 back along the **identity** on the master bundle is **no-op** on **`indexed` /
  `agreedSummit`**.
-/
theorem haltingAnchoredNems_indexedPhantomOps_pullbackAlongDom_id
    {h : HFinalFrameworkWithNEMAnchoredGlue} {hF : h.F₀ = haltingFramework} :
    indexedPhantomCertificateOps_pullbackAlongDom (fun b : HaltingAnchoredFaithfulSummitMasterBundle h hF => b)
        (@haltingAnchoredNemsIndexedPhantomOps h hF) =
      @haltingAnchoredNemsIndexedPhantomOps h hF :=
  indexedPhantomCertificateOps_pullbackAlongDom_id _

/--
  **SPEC_032 Phase D:** iterating NEMS bundle-side pullbacks **agrees** with pullback along the **composite** map —
  functoriality tied to **`NemsFe3SummitBundleCompareSection`** precomposition (see **`RepresentationNemsStageC2`**).
-/
theorem haltingAnchoredNems_indexedPhantomOps_pullbackAlongDom_comp
    {h : HFinalFrameworkWithNEMAnchoredGlue} {hF : h.F₀ = haltingFramework}
    {B' B'' : Type}
    (f : B' → HaltingAnchoredFaithfulSummitMasterBundle h hF)
    (g : B'' → B') :
    indexedPhantomCertificateOps_pullbackAlongDom (f ∘ g) (@haltingAnchoredNemsIndexedPhantomOps h hF) =
      indexedPhantomCertificateOps_pullbackAlongDom g
        (indexedPhantomCertificateOps_pullbackAlongDom f (@haltingAnchoredNemsIndexedPhantomOps h hF)) :=
  indexedPhantomCertificateOps_pullbackAlongDom_comp (@haltingAnchoredNemsIndexedPhantomOps h hF) f g

/--
  **SPEC_032 Phase D:** **`ops'`** on **`B'`** is a **host NEMS pullback** **iff** the forgetful **`summitReportOf`**
  family matches the host and **some** **`f : B' → HaltingAnchoredFaithfulSummitMasterBundle`** realizes **`indexed`** /
  **`agreedSummit`** — cite **`exists_indexedPhantomCertificateOps_pullbackAlongDom_iff`** instantiated at NEMS.
-/
theorem exists_haltingAnchoredNems_indexedPhantomOps_pullbackAlongDom_iff
    {h : HFinalFrameworkWithNEMAnchoredGlue} {hF : h.F₀ = haltingFramework}
    {B' : Type}
    (ops' :
      IndexedPhantomCertificateOps
        NemsPhantomOuterTag B'
        (fun _ω =>
          NEMSHaltingAnchoredSemanticReportCertificate h hF
            (diagonal_barrier_rt haltingFramework (dc := haltingFramework_diagonalCapable)))
        (HaltingAnchoredGluedSummitSemanticReport h hF)) :
    (∃ f : B' → HaltingAnchoredFaithfulSummitMasterBundle h hF,
        ops' = indexedPhantomCertificateOps_pullbackAlongDom f (@haltingAnchoredNemsIndexedPhantomOps h hF)) ↔
      (ops'.summitReportOf = (@haltingAnchoredNemsIndexedPhantomOps h hF).summitReportOf ∧
        ∃ f : B' → HaltingAnchoredFaithfulSummitMasterBundle h hF,
          (∀ (ω : NemsPhantomOuterTag) (b' : B'),
              ops'.indexed ω b' =
                (@haltingAnchoredNemsIndexedPhantomOps h hF).indexed ω (f b')) ∧
            (∀ (b' : B'),
                ops'.agreedSummit b' =
                  (@haltingAnchoredNemsIndexedPhantomOps h hF).agreedSummit (f b'))) :=
  exists_indexedPhantomCertificateOps_pullbackAlongDom_iff (@haltingAnchoredNemsIndexedPhantomOps h hF) ops'

/--
  **SPEC_032 Phase D v3 (conditional):** injective **`agreed_summit`** on the NEMS master bundle **forces** **equality** of
  two **pullback** maps with the **same** pulled **ops**. Not assumed for general **`HaltingAnchoredFaithfulSummitMasterBundle`**
  — see module doc on **`indexedPhantomCertificateOps_pullbackAlongDom_f_eq_of_agreedSummit_injective`**.
-/
theorem haltingAnchoredNems_indexedPhantomOps_pullbackAlongDom_f_eq_of_agreed_summit_injective
    {h : HFinalFrameworkWithNEMAnchoredGlue} {hF : h.F₀ = haltingFramework}
    {B' : Type}
    (h_inj :
      ∀ b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF,
        agreed_summit b₁ = agreed_summit b₂ → b₁ = b₂)
    (f f' : B' → HaltingAnchoredFaithfulSummitMasterBundle h hF)
    (h_eq :
      indexedPhantomCertificateOps_pullbackAlongDom f (@haltingAnchoredNemsIndexedPhantomOps h hF) =
        indexedPhantomCertificateOps_pullbackAlongDom f' (@haltingAnchoredNemsIndexedPhantomOps h hF)) :
    f = f' :=
  indexedPhantomCertificateOps_pullbackAlongDom_f_eq_of_agreedSummit_injective
    (@haltingAnchoredNemsIndexedPhantomOps h hF) h_inj f f' h_eq

theorem haltingAnchoredNems_indexedPhantomOps_pullbackAlongDom_f_unique_of_eq_pullbacks
    {h : HFinalFrameworkWithNEMAnchoredGlue} {hF : h.F₀ = haltingFramework}
    {B' : Type}
    (h_inj :
      ∀ b₁ b₂ : HaltingAnchoredFaithfulSummitMasterBundle h hF,
        agreed_summit b₁ = agreed_summit b₂ → b₁ = b₂)
    (ops' :
      IndexedPhantomCertificateOps
        NemsPhantomOuterTag B'
        (fun _ω =>
          NEMSHaltingAnchoredSemanticReportCertificate h hF
            (diagonal_barrier_rt haltingFramework (dc := haltingFramework_diagonalCapable)))
        (HaltingAnchoredGluedSummitSemanticReport h hF))
    (f f' : B' → HaltingAnchoredFaithfulSummitMasterBundle h hF)
    (hf : ops' = indexedPhantomCertificateOps_pullbackAlongDom f (@haltingAnchoredNemsIndexedPhantomOps h hF))
    (hf' : ops' = indexedPhantomCertificateOps_pullbackAlongDom f' (@haltingAnchoredNemsIndexedPhantomOps h hF)) :
    f = f' :=
  indexedPhantomCertificateOps_pullbackAlongDom_f_unique_of_eq_pullbacks
    (@haltingAnchoredNemsIndexedPhantomOps h hF) h_inj ops' f f' hf hf'

def haltingAnchoredNems_phantomReindex_pullbackAlongDom
    {h : HFinalFrameworkWithNEMAnchoredGlue} {hF : h.F₀ = haltingFramework}
    {B' : Type}
    (f : B' → HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    PhantomReindexLayer
      NemsPhantomOuterTag
      B'
      (fun _ω =>
        NEMSHaltingAnchoredSemanticReportCertificate h hF
          (diagonal_barrier_rt haltingFramework (dc := haltingFramework_diagonalCapable)))
      (HaltingAnchoredGluedSummitSemanticReport h hF)
      (indexedPhantomCertificateOps_pullbackAlongDom f (@haltingAnchoredNemsIndexedPhantomOps h hF)) :=
  phantomReindexLayer_pullbackAlongDom f haltingAnchoredNemsPhantomReindexLayer

theorem haltingAnchoredNems_nonempty_phantomReindex_pullbackAlongDom
    {h : HFinalFrameworkWithNEMAnchoredGlue} {hF : h.F₀ = haltingFramework}
    {B' : Type}
    (f : B' → HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    Nonempty
      (PhantomReindexLayer NemsPhantomOuterTag B'
        (fun _ω =>
          NEMSHaltingAnchoredSemanticReportCertificate h hF
            (diagonal_barrier_rt haltingFramework (dc := haltingFramework_diagonalCapable)))
        (HaltingAnchoredGluedSummitSemanticReport h hF)
        (indexedPhantomCertificateOps_pullbackAlongDom f (@haltingAnchoredNemsIndexedPhantomOps h hF))) :=
  ⟨haltingAnchoredNems_phantomReindex_pullbackAlongDom f⟩

end AdequacyArchitecture.Instances
