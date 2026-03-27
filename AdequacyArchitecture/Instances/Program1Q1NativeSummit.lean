/-
  **SPEC_036_FA1 — FA1-Q4:** native **`CertifiedFrontierRow program1_icCs3CompareQuotient`** (**summit on `Q₁`**).

  **Carrier fact.** The compare kernel for **`icStageD_constantCompareToCorpusBundle.compareToCorpus`** is **total**
  (constant at **`⟨0, by decide⟩`**), hence **`Q₁`** is a **subsingleton** quotient.

  **Summit geometry (IC CS-3–aligned, same scoping as `icCS3HFinal`).**
  * Completed stratified spine **`𝔠`:** **pull back** the corpus **toy** outer row (**`corpusToyLawfulArchitecture`**)
    along **`program1_icCs3CompareQuotient_map`** — outer burden is **`toyBurden`** compare-lifted to **`Q₁`**, so the
    **Fin 2 toy** ridge schematics (**`ToyLikeRidgeOneMode`**) apply verbatim after replaying the three bridge lemmas.
  * **Layer A `P`:** **pull back** **`corpusNemsFin2NonVacuousFinalAdequacy`** (defeq **`icCorpusAlignedNonVacuousFinalAdequacy`**)
    — matches **`program1_icCs3CompareQuotient_pullbackLawful.P`** (**`rfl`** alignment with the named NV 𝒞 row).
  * **`rcp`:** “**both fibers**” predicate on **compare-lifts**. Since **`π`** never hits **`⟨1⟩`**, the second conjunct is
    always **`False`**, so **`holds`** is **never** satisfied — **`NonFlatFinalityFromRouteConstraintFor`** the NV pullback
    **`P`** is immediate once **`∃` final** (same mechanism class as collapsed **both-fibers** tests, but on **`Q₁`** lifts).
-/

import AdequacyArchitecture.Instances.CorpusLawfulRepresentation
import AdequacyArchitecture.Instances.ICCompareRepresentationPullback
import AdequacyArchitecture.Instances.ICNativeOuterClosure
import AdequacyArchitecture.Instances.NEMSBridgeCoreRecord
import AdequacyArchitecture.Lawful.ComparePullback
import AdequacyArchitecture.Lawful.FinalConditionalSummit
import AdequacyArchitecture.Lawful.RidgeBridgeable
import AdequacyArchitecture.Lawful.RidgeSummitStatements
import AdequacyArchitecture.Lawful.StratifiedLawfulArchitecture
import AdequacyArchitecture.Portability.BranchGenericSemanticTransport
import AdequacyArchitecture.Portability.CertifiedFrontierRow
import AdequacyArchitecture.Toy.Fin2Model

namespace AdequacyArchitecture.Instances

open AdequacyArchitecture
open AdequacyArchitecture.Burden (RelocationPair)
open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open AdequacyArchitecture.Portability
open AdequacyArchitecture.Portability.BranchGenericSemanticTransport
open AdequacyArchitecture.Toy
open InfinityCompression.Meta

private abbrev πQ₁ := program1_icCs3CompareQuotient_map

private abbrev βQ₁ := program1_icCs3CompareQuotient

theorem program1_icCs3CompareKernel_total (a b : icNemsSpineCompressionCarrier) :
    program1_icCs3CompareKernel a b := by
  dsimp [program1_icCs3CompareKernel, icStageD_constantCompareToCorpusBundle]

theorem program1_icCs3CompareQuotient_subsingleton : Subsingleton βQ₁ :=
  ⟨by
    intro x y
    induction x using Quot.induction_on with
    | h a =>
      induction y using Quot.induction_on with
      | h b =>
        exact Quot.sound (program1_icCs3CompareKernel_total a b)⟩

theorem program1_icCs3CompareQuotient_map_eq_zero (q : βQ₁) : πQ₁ q = ⟨0, by decide⟩ := by
  induction q using Quot.induction_on with
  | h a =>
    rfl

theorem program1Q1_compareLift_at_one (A : Account βQ₁) :
    compareLiftAccountAlong πQ₁ A (⟨1, by decide⟩ : CorpusStrataCarrier) = False := by
  dsimp [compareLiftAccountAlong]
  apply propext
  constructor
  · rintro ⟨q, hqπ, _⟩
    rw [program1_icCs3CompareQuotient_map_eq_zero q] at hqπ
    simpa using congrArg Fin.val hqπ
  · intro h
    cases h

theorem program1Q1_compareLift_at_zero (A : Account βQ₁) :
    compareLiftAccountAlong πQ₁ A (⟨0, by decide⟩ : CorpusStrataCarrier) ↔ ∃ q : βQ₁, A q := by
  dsimp [compareLiftAccountAlong]
  constructor
  · rintro ⟨q, hqπ, hAq⟩
    rw [program1_icCs3CompareQuotient_map_eq_zero q] at hqπ
    exact ⟨q, hAq⟩
  · rintro ⟨q, hAq⟩
    refine ⟨q, ?_, hAq⟩
    exact program1_icCs3CompareQuotient_map_eq_zero q

/-- Pull back the **corpus toy** 𝒞 row along **`πQ₁`** — outer spine for the **`Q₁`** stratified summit. -/
def program1Q1ToyPullbackLawfulArchitecture : LawfulAdequacyArchitecture βQ₁ :=
  lawfulAdequacyArchitecture_pullbackAlongCompare πQ₁ corpusToyLawfulArchitecture

def program1Q1ToyBurdenVariationSigma :
    Σ' (m : BurdenMode), Σ' (A : Account βQ₁), Σ' (A' : Account βQ₁),
      program1Q1ToyPullbackLawfulArchitecture.B.burden m A ∧
        ¬ program1Q1ToyPullbackLawfulArchitecture.B.burden m A' :=
  ⟨BurdenMode.sem,
    ⟨fun _ => True,
      ⟨fun _ => False,
        And.intro
          (by
            dsimp [program1Q1ToyPullbackLawfulArchitecture, lawfulAdequacyArchitecture_pullbackAlongCompare,
              corpusToyLawfulArchitecture, toyBurden, BurdenPredicates.pullbackAlongCompare]
            let L := compareLiftAccountAlong πQ₁ (fun _ : βQ₁ => True)
            have hL1' : L (⟨1, by decide⟩ : CorpusStrataCarrier) = False := by
              simpa [L] using program1Q1_compareLift_at_one (fun _ : βQ₁ => True)
            have hL0 : L (⟨0, by decide⟩ : CorpusStrataCarrier) := by
              dsimp [compareLiftAccountAlong, L]
              refine ⟨Quot.mk program1_icCs3CompareKernel nemsSpineChain.toArchitecture, ?_, trivial⟩
              exact program1_icCs3CompareQuotient_map_eq_zero _
            show L (⟨0, by decide⟩ : CorpusStrataCarrier) ≠ L (⟨1, by decide⟩ : CorpusStrataCarrier)
            rw [hL1', propext (iff_true_intro hL0)]
            decide)
          (by
            dsimp [program1Q1ToyPullbackLawfulArchitecture, lawfulAdequacyArchitecture_pullbackAlongCompare,
              corpusToyLawfulArchitecture, toyBurden, BurdenPredicates.pullbackAlongCompare, not]
            let L := compareLiftAccountAlong πQ₁ (fun _ : βQ₁ => False)
            have hL0f : ¬ L (⟨0, by decide⟩ : CorpusStrataCarrier) := by
              dsimp [compareLiftAccountAlong, L]
              rintro ⟨_q, _hq, hfalse⟩
              cases hfalse
            have hLf : L (⟨0, by decide⟩ : CorpusStrataCarrier) = False := by
              apply propext
              constructor
              · exact hL0f
              · intro hf
                cases hf
            have hL1' : L (⟨1, by decide⟩ : CorpusStrataCarrier) = False := by
              simpa [L] using program1Q1_compareLift_at_one (fun _ : βQ₁ => False)
            intro hneg
            have h_eq : L (⟨0, by decide⟩ : CorpusStrataCarrier) = L (⟨1, by decide⟩ : CorpusStrataCarrier) := by
              rw [hLf, hL1']
            exact hneg h_eq)⟩⟩⟩

def program1Q1StratifiedLawfulAdequacyArchitecture : StratifiedLawfulAdequacyArchitecture βQ₁ where
  outer := program1Q1ToyPullbackLawfulArchitecture
  burden_variation := program1Q1ToyBurdenVariationSigma

def program1Q1MiddleLayer : LawfulMiddleLayer βQ₁ where
  gluingCompatible := fun _ _ => False
  gluingObstructionAt := fun m A => program1Q1ToyPullbackLawfulArchitecture.B.burden m A

def program1Q1InnerHook : LawfulInnerHook βQ₁ Unit where
  domainResidual := fun A =>
    program1Q1ToyPullbackLawfulArchitecture.B.burden BurdenMode.sem A
  codomainResidual := fun _ => False

def program1Q1CompletedStratifiedLawfulAdequacyArchitecture :
    CompletedStratifiedLawfulAdequacyArchitecture βQ₁ where
  strat := program1Q1StratifiedLawfulAdequacyArchitecture
  compareCodomain := Unit
  compare := fun _ => ()
  middle := program1Q1MiddleLayer
  inner := program1Q1InnerHook

theorem program1Q1_middle_gluingObstructionAt_iff_burden (m : BurdenMode) (A : Account βQ₁) :
    program1Q1MiddleLayer.gluingObstructionAt m A ↔
      program1Q1ToyPullbackLawfulArchitecture.B.burden m A :=
  Iff.rfl

theorem program1Q1_sem_only_burden (m : BurdenMode) (A : Account βQ₁)
    (h : program1Q1ToyPullbackLawfulArchitecture.B.burden m A) : m = BurdenMode.sem := by
  dsimp [program1Q1ToyPullbackLawfulArchitecture, lawfulAdequacyArchitecture_pullbackAlongCompare,
    corpusToyLawfulArchitecture, toyBurden, BurdenPredicates.pullbackAlongCompare] at h
  match m with
  | .sem => rfl
  | .sel => cases h
  | .res => cases h
  | .glue => cases h
  | .cont => cases h
  | .route => cases h

private theorem program1Q1_relocation_pair_toyBurden_pullback_false (m₁ m₂ : BurdenMode) (f : Transform βQ₁)
    (A : Account βQ₁) : ¬ RelocationPair program1Q1ToyPullbackLawfulArchitecture.B m₁ m₂ f A := by
  intro h
  rcases h with ⟨h₁, h₂, h₃⟩
  have hm₁ := program1Q1_sem_only_burden m₁ A h₁
  have hm₂ := program1Q1_sem_only_burden m₂ (f A) h₃
  subst hm₁
  subst hm₂
  exact h₂ h₃

def program1Q1_ridgeToyLikeOneMode : ToyLikeRidgeOneMode program1Q1CompletedStratifiedLawfulAdequacyArchitecture where
  sem_only_burden := program1Q1_sem_only_burden
  no_relocation_pair := program1Q1_relocation_pair_toyBurden_pullback_false

def program1Q1_ridgeBridgeable : RidgeBridgeable program1Q1CompletedStratifiedLawfulAdequacyArchitecture where
  canonicality := canonicality_law_holds _
  ridge_one_mode_schematic := program1Q1_ridgeToyLikeOneMode

theorem program1Q1_outerToInnerBurdenBridgeAt :
    OuterToInnerBurdenBridgeAt program1Q1CompletedStratifiedLawfulAdequacyArchitecture := by
  intro C m A hbd
  match m with
  | .sem =>
    simp only [InnerResidualInducedByCanonical, program1Q1CompletedStratifiedLawfulAdequacyArchitecture,
      program1Q1InnerHook]
    by_cases hadeq : toyPred.adeq AdeqMode.repr (compareLiftAccountAlong πQ₁ (C A))
    · refine Or.inr ⟨hbd, ?_⟩
      dsimp [InnerResidualInducedByCanonical, program1Q1InnerHook, program1Q1ToyPullbackLawfulArchitecture,
        lawfulAdequacyArchitecture_pullbackAlongCompare, corpusToyLawfulArchitecture, toyLawfulArchitecture,
        toyBurden, toyPred, BurdenPredicates.pullbackAlongCompare, AdequacyPredicates.pullbackAlongCompare,
        AdeqMode.repr]
      exact hadeq
    · simp only [program1Q1StratifiedLawfulAdequacyArchitecture, program1Q1ToyPullbackLawfulArchitecture,
        lawfulAdequacyArchitecture_pullbackAlongCompare, corpusToyLawfulArchitecture, toyLawfulArchitecture,
        AdequacyPredicates.pullbackAlongCompare]
      exact Or.inl hadeq
  | .sel => cases hbd
  | .res => cases hbd
  | .glue => cases hbd
  | .cont => cases hbd
  | .route => cases hbd

theorem program1Q1_outerToMiddleBurdenBridgeAt :
    OuterToMiddleBurdenBridgeAt program1Q1CompletedStratifiedLawfulAdequacyArchitecture := by
  intro f m A hbd hyp_adep hyp_drop hex
  match m with
  | .sem =>
    have hnot := hyp_drop A hbd
    rcases hex with ⟨m₂, hm₂⟩
    cases m₂
    · exact (hnot hm₂).elim
    · exact hm₂.elim
    · exact hm₂.elim
    · exact hm₂.elim
    · exact hm₂.elim
    · exact hm₂.elim
  | .sel => cases hbd
  | .res => cases hbd
  | .glue => cases hbd
  | .cont => cases hbd
  | .route => cases hbd

theorem program1Q1_middleInnerBridgeCoherenceAt :
    MiddleInnerBridgeCoherenceAt program1Q1CompletedStratifiedLawfulAdequacyArchitecture := by
  intro m A h
  rcases h with ⟨_hdom, hg⟩
  match m with
  | .sem =>
    have hgl : program1Q1MiddleLayer.gluingObstructionAt BurdenMode.sem A := by
      simpa [program1Q1CompletedStratifiedLawfulAdequacyArchitecture] using hg
    have hm := (program1Q1_middle_gluingObstructionAt_iff_burden BurdenMode.sem A).mp hgl
    convert hm using 1
  | .sel =>
    cases (program1Q1_middle_gluingObstructionAt_iff_burden BurdenMode.sel A).mp
      (by simpa [program1Q1CompletedStratifiedLawfulAdequacyArchitecture] using hg)
  | .res =>
    cases (program1Q1_middle_gluingObstructionAt_iff_burden BurdenMode.res A).mp
      (by simpa [program1Q1CompletedStratifiedLawfulAdequacyArchitecture] using hg)
  | .glue =>
    cases (program1Q1_middle_gluingObstructionAt_iff_burden BurdenMode.glue A).mp
      (by simpa [program1Q1CompletedStratifiedLawfulAdequacyArchitecture] using hg)
  | .cont =>
    cases (program1Q1_middle_gluingObstructionAt_iff_burden BurdenMode.cont A).mp
      (by simpa [program1Q1CompletedStratifiedLawfulAdequacyArchitecture] using hg)
  | .route =>
    cases (program1Q1_middle_gluingObstructionAt_iff_burden BurdenMode.route A).mp
      (by simpa [program1Q1CompletedStratifiedLawfulAdequacyArchitecture] using hg)

theorem program1Q1_carrierPatternInducesRouteConstraintAt :
    CarrierPatternInducesRouteConstraintAt program1Q1CompletedStratifiedLawfulAdequacyArchitecture :=
  carrierPatternInducesRouteConstraintAt_of_ridgeBridgeable program1Q1_ridgeBridgeable

theorem program1Q1_masterStratifiedAdequacyCascadeRidgeAt :
    MasterStratifiedAdequacyCascadeRidgeAt program1Q1CompletedStratifiedLawfulAdequacyArchitecture :=
  ⟨program1Q1_outerToInnerBurdenBridgeAt, program1Q1_outerToMiddleBurdenBridgeAt,
    program1Q1_middleInnerBridgeCoherenceAt, program1Q1_carrierPatternInducesRouteConstraintAt⟩

theorem program1Q1_ridgeCascadeWitness :
    RidgeCascadeWitness program1Q1CompletedStratifiedLawfulAdequacyArchitecture :=
  ridgeCascadeWitness_of_masterStratifiedAdequacyCascadeRidgeAt
    program1Q1_masterStratifiedAdequacyCascadeRidgeAt

/-- Both-fibers test on **compare-lifts** — right fiber is always false, so **`holds` never** holds. -/
def program1Q1RouteProfile : RouteConstraintProfile βQ₁ where
  holds := fun (_f : Transform βQ₁) (A : Account βQ₁) =>
    compareLiftAccountAlong πQ₁ A (⟨0, by decide⟩ : CorpusStrataCarrier) ∧
      compareLiftAccountAlong πQ₁ A (⟨1, by decide⟩ : CorpusStrataCarrier)
  nontrivial := by
    refine ⟨fun _ : βQ₁ => True, id, ?_⟩
    intro hconj
    rcases hconj with ⟨_, h1⟩
    rw [program1Q1_compareLift_at_one (fun _ : βQ₁ => True)] at h1
    cases h1

theorem program1Q1_nonflat :
    NonFlatFinalityFromRouteConstraintFor
      (corpusNemsFin2NonVacuousFinalAdequacy.pullbackAlongCompare πQ₁) program1Q1RouteProfile := by
  intro h
  rcases h with ⟨A, hA⟩
  refine ⟨A, And.intro hA ⟨id, ?_⟩⟩
  intro hbad
  rcases hbad with ⟨_, h1⟩
  rw [program1Q1_compareLift_at_one A] at h1
  cases h1

/-- **Layer A `HFinal` on `Q₁`** — **`P`** aligned with **`program1_icCs3CompareQuotient_pullbackLawful`**. -/
def program1Q1_icCs3HFinal : HFinal βQ₁ :=
  mkHFinal program1Q1CompletedStratifiedLawfulAdequacyArchitecture
    (corpusNemsFin2NonVacuousFinalAdequacy.pullbackAlongCompare πQ₁) program1Q1RouteProfile
    program1Q1_ridgeCascadeWitness program1Q1_nonflat

/-- **FA1-Q4 / SPEC_035 S3b:** native certified frontier row on **`Q₁`**. -/
def certifiedFrontierRow_program1_icCs3CompareQuotient : CertifiedFrontierRow βQ₁ where
  lawful := program1_icCs3CompareQuotient_pullbackLawful
  summitTagged := HFinalWithBranchRole.ofRelocationFinality program1Q1_icCs3HFinal
  summit_lawful_sameAdequacy := rfl
  fe3 := fe3TrivialUnitCore

theorem certifiedFrontierRow_program1_icCs3CompareQuotient_eq_mk :
    certifiedFrontierRow_program1_icCs3CompareQuotient =
      certifiedFrontierRow_of_lawful_summitAligned program1_icCs3CompareQuotient_pullbackLawful
        (HFinalWithBranchRole.ofRelocationFinality program1Q1_icCs3HFinal) rfl :=
  rfl

theorem absoluteFrontierRawS1_program1_icCs3CompareQuotient_via_certifiedRow :
    AbsoluteFrontierRawS1 program1_icCs3CompareQuotient_pullbackLawful.P
      program1_icCs3CompareQuotient_pullbackLawful.B :=
  absoluteFrontierRawS1_of_certifiedFrontierRow certifiedFrontierRow_program1_icCs3CompareQuotient

end AdequacyArchitecture.Instances
