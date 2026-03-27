/-
  **SPEC_031_ZK9 — IC compare representation / pullback** (`icNemsSpineCompressionCarrier`).

  **Stage A.** Native **𝒞** row + **RawS1** by pulling back **`corpusNemsFin2NvLawfulArchitecture`** along
  **`icStageD_constantCompareToCorpusBundle.compareToCorpus`**.

  **Stage B (FE-3 / certificate obstruction).** Generic **collapse** of **`compareLiftAccountAlong`** under a **constant**
  compare — **distinct** native accounts can become **indistinguishable** on the corpus carrier; rich
  **`IndexedPhantomCertificateOps`** along **`π`** are **not** supplied here. The **Unit** trivial **`fe3TrivialUnitCore`**
  remains **definitionally carrier-agnostic** (`BranchGenericSemanticTransport`).

  **Stage C (vs vacuous row).** The CS-3 pullback row **realizes** **`AdeqMode.final`** on some account, whereas
  **`icStageDVacuousOuterPred`** **never** does — so the rows are **not** the same **outer** adequacy.

  **Stage D (packaging).** One **`∧`** bundling **`HFinal`** spine obstruction (**`af1`**), **native RawS1 pullback**,
  corpus **bypass** nonempty, and **Layer A** cascade on **`icCS3HFinal`**.

  **SPEC_032 HM3 (`Instances/NemsSummitCarrierBridge`).** Closed **NEMS** graph bridge + **PI1** / **SA1** for **`icCs3CertifiedFrontierRepresentation`**
  via **`nemsSummitCarrierBridgeCompareAlignment_prodGraph_of_constant_compare`** — see **`SPEC_032_HM3_Q7A_IC_CS3_CONSTANT_COMPARE_HOSTMAP.md`**.
  **SPEC_035 Program 1 / S1a:** **two-step tower** **`comp (corpus Level-2 NV id) icCs3`** = **`icCs3`**; **`hpull`** for cleaving lemmas via **`lawfulAdequacyArchitecture_pullbackAlongCompare_id`**. **Fiber-swap host** outer (**`π = corpusStrataCarrierSwap`**) uses **`corpusNemsFin2NvLawfulArchitecture_pullbackAlong_corpusStrataCarrierSwap`** for **`hpull`** (cleaving **IFF**, not **`comp = icCs3`** — composite compare is **`swap ∘ compareToCorpus`**).
  **SPEC_035 Q3 / S5:** **`icCs3PullbackDisplay_with_host_summitFE3`** — **`IsPullbackDisplay`** ⇒ **native RawS1** **∧** **host** **`summitFE3`** joint (see **`PROGRAM1_S5_MASTER_SWIPE_TEST`**).
  **SPEC_035 S1a+:** **`icCs3CompCorpusNvSwapCertifiedFrontierRepresentation`** (**`comp (swap NV) icCs3`**), **`…_π_apply`**, **`icCs3CompCorpusNvSwap_compareLiftAccountAlong_eq_swap_compareLift`** (**`compareLiftAccountAlong_comp`** factorization), **`icCs3CompCorpusNvSwapCertifiedFrontierRepresentation_not_injectiveCompare`**, **`icStageB_compareLift_collapses_under_comp_corpus_nv_swap_corpus_compare`**, **`icStageC_compareLift_total_true_eq_distinguishing_comp_nv_swap`** (**Stage B/C** — **constant** **`π ↦ ⟨1⟩`** **vs** **`compareToCorpus ↦ ⟨0⟩`**), **`…_isPullbackDisplay`**, **`icCs3CompCorpusNvSwapPullbackDisplay_with_host_summitFE3`**; **`NemsSummitCarrierBridge`** **PI1/SA1** — **`nemsIcCs3CompCorpusNvSwap_graphBridge_mkStandard`**, **`nemsSummitSectionAware_pack_icCs3CompCorpusNvSwap_graph_mkStandard_aligned`** (**no** **`…_injectiveCompareLift`**).
-/

import AdequacyArchitecture.AbsoluteFrontier.AF1_ICNativeSummitFrontier
import AdequacyArchitecture.Instances.ICNativeOuterClosure
import AdequacyArchitecture.Instances.ICStageD
import AdequacyArchitecture.Instances.NEMSBridgeCoreRecord
import AdequacyArchitecture.Lawful.ComparePullback
import AdequacyArchitecture.Lawful.FinalConditionalSummit
import AdequacyArchitecture.Lawful.MasterTheorem
import AdequacyArchitecture.Portability.CertifiedFrontierRow
import AdequacyArchitecture.Portability.SummitRowRepresentation
import AdequacyArchitecture.Toy.Fin2Model

namespace AdequacyArchitecture.Instances

open AdequacyArchitecture
open AdequacyArchitecture.AbsoluteFrontier
open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open AdequacyArchitecture.Summit
open AdequacyArchitecture.Toy
open AdequacyArchitecture.Portability
open AdequacyArchitecture.Portability.BranchGenericSemanticTransport
open AdequacyArchitecture.Portability.CertifiedFrontierRepresentation

/-! ## Stage A — 𝒞 + RawS1 pullback -/

/-- **SPEC_031 Stage A:** Lawful **𝒞** row on the IC compression carrier — **pullback** of **`corpusNemsFin2NvLawfulArchitecture`**. -/
def icNativeCompressionLawfulArchitecture_cs3_pullback : LawfulAdequacyArchitecture icNemsSpineCompressionCarrier :=
  lawfulAdequacyArchitecture_pullbackAlongCompare icStageD_constantCompareToCorpusBundle.compareToCorpus
    corpusNemsFin2NvLawfulArchitecture

theorem icNativeCompression_cs3_pullback_universal_irreducible :
    UniversalIrreducibleAdequacyConjecture icNemsSpineCompressionCarrier
      icNativeCompressionLawfulArchitecture_cs3_pullback.P icNativeCompressionLawfulArchitecture_cs3_pullback.B :=
  universal_irreducible_adequacy_lawful icNativeCompressionLawfulArchitecture_cs3_pullback

theorem icNativeCompression_absoluteFrontierRawS1_cs3_pullback :
    AbsoluteFrontierRawS1 icNativeCompressionLawfulArchitecture_cs3_pullback.P
      icNativeCompressionLawfulArchitecture_cs3_pullback.B :=
  universal_irreducible_adequacy_lawful icNativeCompressionLawfulArchitecture_cs3_pullback

/-! ## SPEC_032 — **`CertifiedFrontierRepresentation`** restatement (nontrivial compare) -/

/-- **Host** = corpus **`Fin 2`**, **native** = IC spine compression carrier; **`π`** = constant corpus compare. -/
def icCs3CertifiedFrontierRepresentation :
    CertifiedFrontierRepresentation icNemsSpineCompressionCarrier CorpusStrataCarrier where
  π := icStageD_constantCompareToCorpusBundle.compareToCorpus
  certified := certifiedFrontierRow_corpus_nems_level2_nv

theorem icCs3CertifiedFrontierRepresentation_isPullbackDisplay :
    icCs3CertifiedFrontierRepresentation.IsPullbackDisplay
      icNativeCompressionLawfulArchitecture_cs3_pullback.P
      icNativeCompressionLawfulArchitecture_cs3_pullback.B :=
  And.intro rfl rfl

/-- Same **RawS1** fact as **`icNativeCompression_absoluteFrontierRawS1_cs3_pullback`**, via **representation** API. -/
theorem icNativeCompression_absoluteFrontierRawS1_cs3_pullback_via_representation :
    AbsoluteFrontierRawS1 icNativeCompressionLawfulArchitecture_cs3_pullback.P
      icNativeCompressionLawfulArchitecture_cs3_pullback.B :=
  absoluteFrontierRawS1_of_valid_certifiedFrontierRepresentation icCs3CertifiedFrontierRepresentation
    icCs3CertifiedFrontierRepresentation_isPullbackDisplay

/--
**SPEC_035 Program 1 / Q3–S5:** **`pullbackDisplay_with_host_summitFE3`** for **IC CS-3** — **native** 𝒞 pullback on the compression carrier
**∧** **host** Stage-C **`summitFE3`** joint law on the shared **`certifiedFrontierRow_corpus_nems_level2_nv`**. **Non-injective** **`π`**
regime (**`compareToCorpus`**); compare **corpus** named packs **`pullbackDisplay_with_host_summitFE3_corpus_nems_level1_id`**, **`pullbackDisplay_with_host_summitFE3_corpus_nems_level2_nv_{id,swap}`** (injective **π** on corpus, **`id`** or **swap**).
-/
theorem icCs3PullbackDisplay_with_host_summitFE3 :
    (AbsoluteFrontierRawS1 icNativeCompressionLawfulArchitecture_cs3_pullback.P
        icNativeCompressionLawfulArchitecture_cs3_pullback.B) ∧
      (MasterStratifiedAdequacyCascadeAt certifiedFrontierRow_corpus_nems_level2_nv.summitTagged.toHFinal.𝔠
          certifiedFrontierRow_corpus_nems_level2_nv.summitTagged.toHFinal.P
          certifiedFrontierRow_corpus_nems_level2_nv.summitTagged.toHFinal.rcp ∧
        ForgetfulIndexedCoherent certifiedFrontierRow_corpus_nems_level2_nv.fe3.ops ∧
        ForgetfulAgreementInjects certifiedFrontierRow_corpus_nems_level2_nv.fe3.ops) :=
  pullbackDisplay_with_host_summitFE3 icCs3CertifiedFrontierRepresentation_isPullbackDisplay

/-! ## SPEC_032 Stage B — injective compare **fails** on IC constant corpus compare (sharp boundary example) -/

theorem ic_compareToCorpus_not_injective :
    ¬ Function.Injective icStageD_constantCompareToCorpusBundle.compareToCorpus := by
  intro h
  rcases ic_nems_spine_compression_carrier_nontrivial with ⟨b₁, b₂, hbne⟩
  refine hbne (h ?_)
  rfl

theorem icCs3CertifiedFrontierRepresentation_not_injectiveCompare :
    ¬ CertifiedFrontierRepresentation.HasInjectiveCompare icCs3CertifiedFrontierRepresentation := by
  simpa [icCs3CertifiedFrontierRepresentation, CertifiedFrontierRepresentation.HasInjectiveCompare]
    using ic_compareToCorpus_not_injective

/-! ## Stage B — compare-collapse (constant corpus compare) -/

theorem icStageB_compareLift_collapses_under_constant_corpus_compare :
    ∃ A₁ A₂ : Account icNemsSpineCompressionCarrier, A₁ ≠ A₂ ∧
      compareLiftAccountAlong icStageD_constantCompareToCorpusBundle.compareToCorpus A₁ =
        compareLiftAccountAlong icStageD_constantCompareToCorpusBundle.compareToCorpus A₂ :=
  compareLiftAccountAlong_collapses_of_constant icStageD_constantCompareToCorpusBundle.compareToCorpus
    ⟨0, by decide⟩ (fun _ => rfl) ic_nems_spine_compression_carrier_nontrivial

/-! ## Stage C — CS-3 pullback vs Stage-D vacuous outer -/

theorem icStageC_compareLift_total_true_eq_distinguishing :
    compareLiftAccountAlong icStageD_constantCompareToCorpusBundle.compareToCorpus
        (fun _ : icNemsSpineCompressionCarrier => True) =
      distinguishingAccount := by
  funext i
  rcases ic_nems_spine_compression_carrier_nontrivial with ⟨b₀, b₁, hbne⟩
  by_cases hi : i = 0
  · subst hi
    dsimp [compareLiftAccountAlong, icStageD_constantCompareToCorpusBundle, distinguishingAccount]
    apply propext
    constructor
    · rintro ⟨_, hb, _⟩
      simp
    · intro _
      refine ⟨b₀, ?_, trivial⟩
      rfl
  · have hi1 : i = 1 := by
      rcases i with ⟨iv, ivlt⟩
      interval_cases iv
      · exact absurd (Fin.ext rfl) hi
      · rfl
    subst hi1
    dsimp [compareLiftAccountAlong, icStageD_constantCompareToCorpusBundle, distinguishingAccount]
    apply propext
    refine iff_of_false ?_ ?_
    · rintro ⟨b, hb, _⟩
      simp at hb
    · intro h
      cases h

theorem icStageC_cs3_pullback_realizes_final_adequacy :
    ∃ A : Account icNemsSpineCompressionCarrier,
      icNativeCompressionLawfulArchitecture_cs3_pullback.P.adeq AdeqMode.final A := by
  refine ⟨fun _ => True, ?_⟩
  suffices corpusNemsFin2NonVacuousFinalAdequacy.adeq AdeqMode.final
      (compareLiftAccountAlong icStageD_constantCompareToCorpusBundle.compareToCorpus
        (fun _ : icNemsSpineCompressionCarrier => True)) by
    simpa [icNativeCompressionLawfulArchitecture_cs3_pullback, lawfulAdequacyArchitecture_pullbackAlongCompare,
      corpusNemsFin2NvLawfulArchitecture, AdequacyPredicates.pullbackAlongCompare]
  rw [icStageC_compareLift_total_true_eq_distinguishing]
  simp only [corpusNemsFin2NonVacuousFinalAdequacy]
  simpa using distinguishing_ne

theorem icStageC_cs3_pullback_ne_icStageDVacuousOuterPred :
    icNativeCompressionLawfulArchitecture_cs3_pullback.P ≠ icStageDVacuousOuterPred icNemsSpineCompressionCarrier := by
  intro he
  rcases icStageC_cs3_pullback_realizes_final_adequacy with ⟨A, hA⟩
  have hv : ¬ (icStageDVacuousOuterPred icNemsSpineCompressionCarrier).adeq AdeqMode.final A := by
    simp [icStageDVacuousOuterPred]
  have h := congrArg (fun P : AdequacyPredicates icNemsSpineCompressionCarrier => P.adeq AdeqMode.final A) he
  exact hv (Eq.mp h hA)

theorem icStageC_vacuous_s1_lawful_ne_cs3_pullback_s1_lawful :
    S1LawfulFrontierRow.ofLawful (icStageDVacuousLawful icNemsSpineCompressionCarrier) ≠
      S1LawfulFrontierRow.ofLawful icNativeCompressionLawfulArchitecture_cs3_pullback := by
  intro he
  have hl := congrArg S1LawfulFrontierRow.lawful he
  have hP := congrArg LawfulAdequacyArchitecture.P hl
  exact icStageC_cs3_pullback_ne_icStageDVacuousOuterPred (Eq.symm hP)

/-! ## Stage D — AF-1 + native pullbacks (single cite) -/

/--
**SPEC_031 Stage D:** **Layer A checklist** obstruction on the compression carrier, **parallel** native **RawS1** on the
same carrier via CS-3 compare pullback, and the **honest corpus bypass** (**`ICSummitContractBypassWitness`**) with
**`icCS3HFinal`** cascade — the **complete** current-repo IC representation story without smuggling **`HFinal`** onto
**`CompressionArchitecture`**.
-/
theorem icSpec031_stageD_resolution_pack :
    (Nonempty (HFinal icNemsSpineCompressionCarrier) ↔
        ∃ (𝔠 : CompletedStratifiedLawfulAdequacyArchitecture icNemsSpineCompressionCarrier)
          (P : AdequacyPredicates icNemsSpineCompressionCarrier)
          (rcp : RouteConstraintProfile icNemsSpineCompressionCarrier) (_ : RidgeCascadeWitness 𝔠)
          (_ : NonFlatFinalityFromRouteConstraintFor P rcp), True) ∧
      AbsoluteFrontierRawS1 icNativeCompressionLawfulArchitecture_cs3_pullback.P
        icNativeCompressionLawfulArchitecture_cs3_pullback.B ∧
      Nonempty ICSummitContractBypassWitness ∧
      MasterStratifiedAdequacyCascadeAt icCS3HFinal.𝔠 icCS3HFinal.P icCS3HFinal.rcp :=
  And.intro af1_ic_branch_obstruction_and_standard_summit_entry.1
    (And.intro icNativeCompression_absoluteFrontierRawS1_cs3_pullback af1_ic_branch_obstruction_and_standard_summit_entry.2)

/-! ## SPEC_035 Program 1 — two-step compare tower (**corpus `id` host** ∘ **IC CS-3 compare**) -/

/--
**Chain hypothesis** for **`isPullbackDisplay_comp_iff_of_pulledBackInner`:** **IC CS-3** uses the **same** corpus **`CertifiedFrontierRow`**
as **`certifiedFrontierRepresentation_corpus_nems_level2_nv_id`**, so the **host lawful** side of **`hpull`** is **`id`**-pullback
of the **identity** corpus repr’s host — hence **`lawfulAdequacyArchitecture_pullbackAlongCompare_id`**.
-/
theorem icCs3CertifiedFrontierRepresentation_pullbackHostLawful_eq_id_corpus_host :
    icCs3CertifiedFrontierRepresentation.certified.lawful =
      lawfulAdequacyArchitecture_pullbackAlongCompare
        (id : CorpusStrataCarrier → CorpusStrataCarrier)
        certifiedFrontierRepresentation_corpus_nems_level2_nv_id.certified.lawful := by
  simp [icCs3CertifiedFrontierRepresentation, certifiedFrontierRepresentation_corpus_nems_level2_nv_id,
    lawfulAdequacyArchitecture_pullbackAlongCompare_id]

/-- **Factorization:** **IC CS-3** repr **`π`** is **`id` ∘ compareToCorpus`**, same corpus **host** row as the **identity** corpus repr. -/
theorem icCs3CertifiedFrontierRepresentation_eq_comp_corpus_nems_level2_nv_id :
    comp certifiedFrontierRepresentation_corpus_nems_level2_nv_id icCs3CertifiedFrontierRepresentation =
      icCs3CertifiedFrontierRepresentation :=
  rfl

/--
**Cleaving rephrase:** **`IsPullbackDisplay`** for the **one-step** IC repr is **equivalent** to **`IsPullbackDisplay`** for
the **composed** repr (**`comp`**), by **`isPullbackDisplay_comp_iff_of_pulledBackInner`** — here a **bookkeeping**
instantiation (both sides reduce to the **same** one-step display).
-/
theorem icCs3PullbackDisplay_iff_comp_corpusIdTower_isPullbackDisplay (P : AdequacyPredicates icNemsSpineCompressionCarrier)
    (B : BurdenPredicates icNemsSpineCompressionCarrier) :
    icCs3CertifiedFrontierRepresentation.IsPullbackDisplay P B ↔
      (comp certifiedFrontierRepresentation_corpus_nems_level2_nv_id icCs3CertifiedFrontierRepresentation).IsPullbackDisplay
        P B :=
  isPullbackDisplay_comp_iff_of_pulledBackInner certifiedFrontierRepresentation_corpus_nems_level2_nv_id
    icCs3CertifiedFrontierRepresentation icCs3CertifiedFrontierRepresentation_pullbackHostLawful_eq_id_corpus_host

/--
**Chain hypothesis (swap host):** **IC CS-3** `certified.lawful` is the corpus **Level-2 NV** row, **definitionally** unchanged by
𝒞-pullback along **`corpusStrataCarrierSwap`** — **`corpusNemsFin2NvLawfulArchitecture_pullbackAlong_corpusStrataCarrierSwap`**.
-/
theorem icCs3CertifiedFrontierRepresentation_pullbackHostLawful_eq_swap_corpus_host :
    icCs3CertifiedFrontierRepresentation.certified.lawful =
      lawfulAdequacyArchitecture_pullbackAlongCompare corpusStrataCarrierSwap
        certifiedFrontierRepresentation_corpus_nems_level2_nv_swap.certified.lawful :=
  Eq.symm corpusNemsFin2NvLawfulArchitecture_pullbackAlong_corpusStrataCarrierSwap

/--
**Cleaving (swap outer):** **`IsPullbackDisplay`** along **`compareToCorpus`** iff along **`corpusStrataCarrierSwap ∘ compareToCorpus`**
for the same native **`(P,B)`**, matching **`isPullbackDisplay_comp_iff_of_pulledBackInner`**.
-/
theorem icCs3PullbackDisplay_iff_comp_corpusSwapTower_isPullbackDisplay (P : AdequacyPredicates icNemsSpineCompressionCarrier)
    (B : BurdenPredicates icNemsSpineCompressionCarrier) :
    icCs3CertifiedFrontierRepresentation.IsPullbackDisplay P B ↔
      (comp certifiedFrontierRepresentation_corpus_nems_level2_nv_swap icCs3CertifiedFrontierRepresentation).IsPullbackDisplay
        P B :=
  isPullbackDisplay_comp_iff_of_pulledBackInner certifiedFrontierRepresentation_corpus_nems_level2_nv_swap
    icCs3CertifiedFrontierRepresentation icCs3CertifiedFrontierRepresentation_pullbackHostLawful_eq_swap_corpus_host

/-- **SPEC_035 Program 1 / S1a:** composed compare **`corpusStrataCarrierSwap ∘ compareToCorpus`** (outer **swap** tower). -/
abbrev icCs3CompCorpusNvSwapCertifiedFrontierRepresentation :
    CertifiedFrontierRepresentation icNemsSpineCompressionCarrier CorpusStrataCarrier :=
  comp certifiedFrontierRepresentation_corpus_nems_level2_nv_swap icCs3CertifiedFrontierRepresentation

theorem icCs3CompCorpusNvSwapCertifiedFrontierRepresentation_π_apply (x : icNemsSpineCompressionCarrier) :
    icCs3CompCorpusNvSwapCertifiedFrontierRepresentation.π x = ⟨1, by decide⟩ := by
  simp [icCs3CompCorpusNvSwapCertifiedFrontierRepresentation, CertifiedFrontierRepresentation.comp,
    certifiedFrontierRepresentation_corpus_nems_level2_nv_swap, icCs3CertifiedFrontierRepresentation,
    icStageD_constantCompareToCorpusBundle, Function.comp_apply, corpusStrataCarrierSwap]

theorem icCs3CompCorpusNvSwapCertifiedFrontierRepresentation_not_injectiveCompare :
    ¬ CertifiedFrontierRepresentation.HasInjectiveCompare icCs3CompCorpusNvSwapCertifiedFrontierRepresentation := by
  intro h
  rcases ic_nems_spine_compression_carrier_nontrivial with ⟨b₁, b₂, hbne⟩
  refine hbne (h ?_)
  rw [icCs3CompCorpusNvSwapCertifiedFrontierRepresentation_π_apply,
    icCs3CompCorpusNvSwapCertifiedFrontierRepresentation_π_apply]

/--
**Stage B (swap ∘ compare tower):** same **compare-lift collapse** mechanism as **`icStageB_compareLift_collapses_under_constant_corpus_compare`**
— **`π`** is **constant** at **`⟨1⟩`** (**`icCs3CompCorpusNvSwapCertifiedFrontierRepresentation_π_apply`**).
-/
theorem icStageB_compareLift_collapses_under_comp_corpus_nv_swap_corpus_compare :
    ∃ A₁ A₂ : Account icNemsSpineCompressionCarrier, A₁ ≠ A₂ ∧
      compareLiftAccountAlong icCs3CompCorpusNvSwapCertifiedFrontierRepresentation.π A₁ =
        compareLiftAccountAlong icCs3CompCorpusNvSwapCertifiedFrontierRepresentation.π A₂ :=
  compareLiftAccountAlong_collapses_of_constant icCs3CompCorpusNvSwapCertifiedFrontierRepresentation.π
    ⟨1, by decide⟩ (fun _ => icCs3CompCorpusNvSwapCertifiedFrontierRepresentation_π_apply _)
    ic_nems_spine_compression_carrier_nontrivial

/--
**SPEC_035 Program 1:** **Account**-layer factorization of **compare-lift** along **`comp (corpus NV swap) icCs3`**
— **`compareLiftAccountAlong_comp`** on **`corpusStrataCarrierSwap ∘ compareToCorpus`**.
-/
theorem icCs3CompCorpusNvSwap_compareLiftAccountAlong_eq_swap_compareLift (A : Account icNemsSpineCompressionCarrier) :
    compareLiftAccountAlong icCs3CompCorpusNvSwapCertifiedFrontierRepresentation.π A =
      compareLiftAccountAlong corpusStrataCarrierSwap
        (compareLiftAccountAlong icStageD_constantCompareToCorpusBundle.compareToCorpus A) := by
  rw [← compareLiftAccountAlong_comp]
  rfl

/--
**Stage C (swap ∘ compare tower):** **total** native **`True`** lifts to **`distinguishingAccount ∘ corpusStrataCarrierSwap`**
on **`CorpusStrataCarrier`** — **0/1** fibers **swapped** relative to **`icStageC_compareLift_total_true_eq_distinguishing`**
(**`compareToCorpus`** constant at **`⟨0⟩`**). *Proof:* **`icCs3CompCorpusNvSwap_compareLiftAccountAlong_eq_swap_compareLift`**
+ **`icStageC_compareLift_total_true_eq_distinguishing`** + **`compareLiftAccountAlong_corpusStrataCarrierSwap`** (**pointwise**, **`NEMSBridgeCoreRecord`**).
-/
theorem icStageC_compareLift_total_true_eq_distinguishing_comp_nv_swap :
    compareLiftAccountAlong icCs3CompCorpusNvSwapCertifiedFrontierRepresentation.π
        (fun _ : icNemsSpineCompressionCarrier => True) =
      fun i : CorpusStrataCarrier => distinguishingAccount (corpusStrataCarrierSwap i) := by
  rw [icCs3CompCorpusNvSwap_compareLiftAccountAlong_eq_swap_compareLift,
    icStageC_compareLift_total_true_eq_distinguishing]
  funext i
  exact compareLiftAccountAlong_corpusStrataCarrierSwap distinguishingAccount i

theorem icCs3CompCorpusNvSwapCertifiedFrontierRepresentation_isPullbackDisplay :
    icCs3CompCorpusNvSwapCertifiedFrontierRepresentation.IsPullbackDisplay
      icNativeCompressionLawfulArchitecture_cs3_pullback.P
      icNativeCompressionLawfulArchitecture_cs3_pullback.B :=
  (icCs3PullbackDisplay_iff_comp_corpusSwapTower_isPullbackDisplay
      icNativeCompressionLawfulArchitecture_cs3_pullback.P
      icNativeCompressionLawfulArchitecture_cs3_pullback.B).mp
    icCs3CertifiedFrontierRepresentation_isPullbackDisplay

/--
**SPEC_035 Q3 / S5:** same **parallel** **`pullbackDisplay_with_host_summitFE3`** conclusion as **one-step** **IC CS-3**, for the
**composed** **swap ∘ compare** representation (**`certified`** is still **`certifiedFrontierRow_corpus_nems_level2_nv`**).
-/
theorem icCs3CompCorpusNvSwapPullbackDisplay_with_host_summitFE3 :
    (AbsoluteFrontierRawS1 icNativeCompressionLawfulArchitecture_cs3_pullback.P
        icNativeCompressionLawfulArchitecture_cs3_pullback.B) ∧
      (MasterStratifiedAdequacyCascadeAt certifiedFrontierRow_corpus_nems_level2_nv.summitTagged.toHFinal.𝔠
          certifiedFrontierRow_corpus_nems_level2_nv.summitTagged.toHFinal.P
          certifiedFrontierRow_corpus_nems_level2_nv.summitTagged.toHFinal.rcp ∧
        ForgetfulIndexedCoherent certifiedFrontierRow_corpus_nems_level2_nv.fe3.ops ∧
        ForgetfulAgreementInjects certifiedFrontierRow_corpus_nems_level2_nv.fe3.ops) :=
  pullbackDisplay_with_host_summitFE3 icCs3CompCorpusNvSwapCertifiedFrontierRepresentation_isPullbackDisplay

/-!
## SPEC_035 Program 1 / S3b — compare-fiber quotient canary **`Q₁`** (**IC CS-3** stress anchor)

**Advisor `Q₁`:** quotient **`X/~π`** where **`π = compareToCorpus`** and **`X = icNemsSpineCompressionCarrier`**.

**Route A (𝒞 row):** predicates on **`Q₁`** are **literally** **`pullbackAlongCompare`** of the **named corpus host** along the
**canonical** **`Quot.lift`** map — **§8.4**-clean (**no** **RawS1** / **HFinal** in **`def`**). **Representation** packaging
reuses the **same** **`certifiedFrontierRow_corpus_nems_level2_nv`** as **`icCs3CertifiedFrontierRepresentation`**.

**Native summit row (FA1-Q4):** **`CertifiedFrontierRow program1_icCs3CompareQuotient`** is **`certifiedFrontierRow_program1_icCs3CompareQuotient`**
in **`Instances/Program1Q1NativeSummit.lean`** (toy-pullback stratified spine + **`HFinal`** **`program1Q1_icCs3HFinal`**, RawS1 corollary).
The **external** packaging **`CertifiedFrontierRepresentation Q₁ CorpusStrataCarrier`** (**`program1_icCs3CompareQuotientRepr`**) remains the **representation** route.

See **`PROGRAM1_S3B_HONEST_QUOTIENT`** / **`WQ-Q4`** audit resolution; **`SPEC_036_FA1`** **FA1-Q4** closure.
-/

/-- Compare-fiber indistinguishability — **kernel** of **`icStageD_constantCompareToCorpusBundle.compareToCorpus`**. -/
def program1_icCs3CompareKernel (a b : icNemsSpineCompressionCarrier) : Prop :=
  icStageD_constantCompareToCorpusBundle.compareToCorpus a =
    icStageD_constantCompareToCorpusBundle.compareToCorpus b

/-- **Advisor `Q₁`** on the **IC CS-3** compression carrier. -/
abbrev program1_icCs3CompareQuotient : Type :=
  Quot program1_icCs3CompareKernel

/-- **Induced compare** **`Q₁ → CorpusStrataCarrier`** (**well-defined** by **`Quot.lift`**). -/
def program1_icCs3CompareQuotient_map : program1_icCs3CompareQuotient → CorpusStrataCarrier :=
  Quot.lift icStageD_constantCompareToCorpusBundle.compareToCorpus fun _ _ h => h

theorem program1_icCs3CompareQuotient_map_injective :
    Function.Injective program1_icCs3CompareQuotient_map := by
  intro q₁ q₂ h
  induction q₁ using Quot.induction_on with
  | h a =>
    induction q₂ using Quot.induction_on with
    | h b =>
      replace h : icStageD_constantCompareToCorpusBundle.compareToCorpus a =
          icStageD_constantCompareToCorpusBundle.compareToCorpus b := by
        simpa [program1_icCs3CompareQuotient_map, Quot.lift_mk] using h
      exact Quot.sound h

/-- **`LawfulAdequacyArchitecture Q₁`** via **honest** compare-pullback along **`program1_icCs3CompareQuotient_map`**. -/
def program1_icCs3CompareQuotient_pullbackLawful : LawfulAdequacyArchitecture program1_icCs3CompareQuotient :=
  lawfulAdequacyArchitecture_pullbackAlongCompare program1_icCs3CompareQuotient_map
    corpusNemsFin2NvLawfulArchitecture

theorem program1_icCs3CompareQuotient_pullback_absoluteFrontierRawS1 :
    AbsoluteFrontierRawS1 program1_icCs3CompareQuotient_pullbackLawful.P
      program1_icCs3CompareQuotient_pullbackLawful.B :=
  universal_irreducible_adequacy_lawful program1_icCs3CompareQuotient_pullbackLawful

/-- Same **`repr`** host as **`icCs3CertifiedFrontierRepresentation`**; compare is the **quotient lift** of **`compareToCorpus`**. -/
def program1_icCs3CompareQuotientRepr :
    CertifiedFrontierRepresentation program1_icCs3CompareQuotient CorpusStrataCarrier where
  π := program1_icCs3CompareQuotient_map
  certified := certifiedFrontierRow_corpus_nems_level2_nv

theorem program1_icCs3CompareQuotientRepr_isPullbackDisplay :
    program1_icCs3CompareQuotientRepr.IsPullbackDisplay
      program1_icCs3CompareQuotient_pullbackLawful.P
      program1_icCs3CompareQuotient_pullbackLawful.B :=
  And.intro rfl rfl

theorem program1_icCs3CompareQuotient_injectiveCompare :
    program1_icCs3CompareQuotientRepr.HasInjectiveCompare :=
  program1_icCs3CompareQuotient_map_injective

/--
**Parallel** **S5** packaging on **`Q₁`**: **native** **RawS1** on the **pullback** **𝒞** row **∧** **host** **`summitFE3`**
(the **same** conclusion pattern as **`icCs3PullbackDisplay_with_host_summitFE3`**, carrier **`Q₁`**).
-/
theorem program1_icCs3CompareQuotient_pullbackDisplay_with_host_summitFE3 :
    (AbsoluteFrontierRawS1 program1_icCs3CompareQuotient_pullbackLawful.P
        program1_icCs3CompareQuotient_pullbackLawful.B) ∧
      (MasterStratifiedAdequacyCascadeAt certifiedFrontierRow_corpus_nems_level2_nv.summitTagged.toHFinal.𝔠
          certifiedFrontierRow_corpus_nems_level2_nv.summitTagged.toHFinal.P
          certifiedFrontierRow_corpus_nems_level2_nv.summitTagged.toHFinal.rcp ∧
        ForgetfulIndexedCoherent certifiedFrontierRow_corpus_nems_level2_nv.fe3.ops ∧
        ForgetfulAgreementInjects certifiedFrontierRow_corpus_nems_level2_nv.fe3.ops) :=
  pullbackDisplay_with_host_summitFE3 program1_icCs3CompareQuotientRepr_isPullbackDisplay

end AdequacyArchitecture.Instances
