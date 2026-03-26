/-
  **SPEC_029_FR1 — FE-2 (IC):** typed status — **no** canonical **`BranchGenericSemanticTransport.Core`**
  on the faithful IC **`From*`** artifact without additional summit spine data.

  **Theorem-fed artifact.** `ICFaithful.lean` — `faithfulICNEMSSpineCertificationLayer` /
  `nonempty_faithful_ic_nems_spine_certification_layer` (inner **`CertificationLayer`** on
  **`CompressionArchitecture`**).

  **FE-3 shape.** `Core` / **`IndexedPhantomCertificateOps`** for NEMS use bundle
  **`HaltingAnchoredFaithfulSummitMasterBundle`** and payload **`HaltingAnchoredGluedSummitSemanticReport`**.
  The IC layer’s fields (`EnrichedIrreducibility`, `CanonicalBareCertificate`, …) are **not** that report type,
  and this package exports **no** morphism from `Inner.CertificationLayer _` to that payload by definition.

  **Machine-checked obstruction (pullback form).** Native **`HFinal`** on the IC Phase-1 carrier is **iff**
  producing a full completed stratified spine + ridge + non-flat witness on that carrier — not merely an inner
  layer. That is exactly the “compare-map / representation gap” recorded for **`ICOuterClosureRepresentationCompare`**.

  **FE-2+ (routing).** A future IC **`Core`** parallel to **NEMS** would extend that compare-map structure with
  witnessed predicate/ridge pullbacks (TODO on the compare bundle). Until then, cite **`ic_fe2_no_hfinal_from_layer_only`** +
  **`ICOuterClosureRepresentationCompare`** doc.

  **SPEC_032 Phase D (Law X analogue).** **`NemsFe3SummitBundleCompareSection`** and **`ApsFe3MiddleBundleCompareSection`**
  name explicit **`proj : B_γ → Bundle`**. IC has **no** matching theorem-fed **`IndexedPhantomCertificateOps`** host on a
  fixed bundle type here — so **no** IC **`IcFe3…CompareSection`** layer is introduced until an IC-native FE-3 witness exists.
  **`CertifiedFrontierRepresentation`** + **`IsPullbackDisplay`** still **do not** construct **any** such **`proj`** (same
  obstruction as NEMS / APS: compare **`π`** vs bundle morphism).
-/

import AdequacyArchitecture.Instances.ICNativeOuterClosure

namespace AdequacyArchitecture.Instances

open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit

/-- Re-export: IC native summit row requires the **same** stratified closure package as any `HFinal`, not the
inner `From*` layer alone. Use this as the **sharp** “no cheap `Core`” guardrail. -/
theorem ic_fe2_no_hfinal_from_layer_only :
    Nonempty (HFinal icNemsSpineCompressionCarrier) ↔
      ∃ (𝔠 : CompletedStratifiedLawfulAdequacyArchitecture icNemsSpineCompressionCarrier)
        (P : AdequacyPredicates icNemsSpineCompressionCarrier)
        (rcp : RouteConstraintProfile icNemsSpineCompressionCarrier) (_ : RidgeCascadeWitness 𝔠)
        (_ : NonFlatFinalityFromRouteConstraintFor P rcp), True :=
  ic_phase1_nonempty_hfinal_iff_spine_data

end AdequacyArchitecture.Instances
