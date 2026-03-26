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

end AdequacyArchitecture.Instances
