/-
  **SPEC_029_FR1 — FE-2 (APS+):** a **minimal** **`BranchGenericSemanticTransport.Core`** on
  **`Middle.RealizationLayer Unit`** — middle-band “indexed composition” as both certificate and forgetful
  payload (`ICompIdx`).

  This is **not** the NEMS halting-anchored story; it shows how **theorem-fed APS** discharge can
  **instantiate** the same *abstract* FE-3 vocabulary with **`R := Prop`** and phantom slot **`Unit`**.

  **Faithful cross-corpus** witness: **`faithfulAPSCrossCorpusRealizationLayer`** satisfies the same
  coherence/injectivity laws as any other instance of **`Middle.RealizationLayer Unit`**.
-/

import AdequacyArchitecture.Instances.APSFaithful
import AdequacyArchitecture.Portability.BranchGenericSemanticTransport
import ReflexiveArchitecture.Middle.Interface

namespace AdequacyArchitecture.Instances

open AdequacyArchitecture.Portability.BranchGenericSemanticTransport
open ReflexiveArchitecture
open ReflexiveArchitecture.Middle

/-- Phantom index for middle-only transport (`Unit` carrier). -/
abbrev ApsMiddlePhantomTag : Type :=
  _root_.Unit

/-- **FE-3-shaped ops:** certificate at `ω` is **`M.ICompIdx`**; forgetful report is the proposition itself. -/
def apsUnitMiddleIndexedPhantomOps :
    IndexedPhantomCertificateOps ApsMiddlePhantomTag (RealizationLayer Unit) (fun _ => Prop) Prop where
  indexed := fun _ (M : RealizationLayer Unit) => M.ICompIdx
  summitReportOf := fun _w (p : Prop) => p
  agreedSummit := fun (M : RealizationLayer Unit) => M.ICompIdx

theorem aps_unit_middle_forget_coherent : ForgetfulIndexedCoherent apsUnitMiddleIndexedPhantomOps := by
  intro _w M
  rfl

theorem aps_unit_middle_forget_injects : ForgetfulAgreementInjects apsUnitMiddleIndexedPhantomOps :=
  fun _ _ _ _ h => h

def apsUnitMiddleBranchGenericCore :
    Core ApsMiddlePhantomTag (RealizationLayer Unit) (fun _ => Prop) Prop where
  ops := apsUnitMiddleIndexedPhantomOps
  forget_coherent := aps_unit_middle_forget_coherent
  forget_injects := aps_unit_middle_forget_injects

def apsUnitMiddlePhantomReindexLayer :
    PhantomReindexLayer ApsMiddlePhantomTag (RealizationLayer Unit) (fun _ => Prop) Prop
      apsUnitMiddleIndexedPhantomOps where
  reindex := fun {_ _} _ p => p
  forget_reindex := fun {_ _} _ _ => rfl

theorem aps_fe2_faithful_agreed_summit_icomp :
    apsUnitMiddleBranchGenericCore.ops.agreedSummit faithfulAPSCrossCorpusRealizationLayer =
      faithfulAPSCrossCorpusRealizationLayer.ICompIdx :=
  rfl

theorem aps_fe2_faithful_summitReportOf_indexed_eq_agreed :
    @IndexedPhantomCertificateOps.summitReportOf _ _ _ _ apsUnitMiddleIndexedPhantomOps ()
      (apsUnitMiddleIndexedPhantomOps.indexed () faithfulAPSCrossCorpusRealizationLayer) =
      apsUnitMiddleBranchGenericCore.ops.agreedSummit faithfulAPSCrossCorpusRealizationLayer :=
  rfl

/-- **SPEC_032 Phase D:** APS **middle** FE-3 — bundle-side pullback **id** / **comp** / characterization (**`iff`**). -/
theorem apsUnitMiddle_indexedPhantomOps_pullbackAlongDom_id :
    indexedPhantomCertificateOps_pullbackAlongDom (fun b : RealizationLayer Unit => b) apsUnitMiddleIndexedPhantomOps =
      apsUnitMiddleIndexedPhantomOps :=
  indexedPhantomCertificateOps_pullbackAlongDom_id _

theorem apsUnitMiddle_indexedPhantomOps_pullbackAlongDom_comp {B' B'' : Type}
    (f : B' → RealizationLayer Unit)
    (g : B'' → B') :
    indexedPhantomCertificateOps_pullbackAlongDom (f ∘ g) apsUnitMiddleIndexedPhantomOps =
      indexedPhantomCertificateOps_pullbackAlongDom g
        (indexedPhantomCertificateOps_pullbackAlongDom f apsUnitMiddleIndexedPhantomOps) :=
  indexedPhantomCertificateOps_pullbackAlongDom_comp apsUnitMiddleIndexedPhantomOps f g

theorem exists_apsUnitMiddle_indexedPhantomOps_pullbackAlongDom_iff {B' : Type}
    (ops' : IndexedPhantomCertificateOps ApsMiddlePhantomTag B' (fun _ => Prop) Prop) :
    (∃ f : B' → RealizationLayer Unit,
        ops' = indexedPhantomCertificateOps_pullbackAlongDom f apsUnitMiddleIndexedPhantomOps) ↔
      (ops'.summitReportOf = apsUnitMiddleIndexedPhantomOps.summitReportOf ∧
        ∃ f : B' → RealizationLayer Unit,
          (∀ (ω : ApsMiddlePhantomTag) (b' : B'),
              ops'.indexed ω b' = apsUnitMiddleIndexedPhantomOps.indexed ω (f b')) ∧
            (∀ (b' : B'), ops'.agreedSummit b' = apsUnitMiddleIndexedPhantomOps.agreedSummit (f b'))) :=
  exists_indexedPhantomCertificateOps_pullbackAlongDom_iff apsUnitMiddleIndexedPhantomOps ops'

end AdequacyArchitecture.Instances
