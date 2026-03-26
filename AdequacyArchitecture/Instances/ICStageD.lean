/-
  **SPEC_030_MX7 — Stage D (IC native / representation).**

  **Question (honest):** can the **IC NEMS spine compression** carrier enter the **`S1LawfulFrontierRow` /
  `CertifiedFrontierRow` / `SummitFE3SemanticPackage`** world **natively** with the same proof-essential content as
  the CS-3 corpus row, or only after a **representation** step (compare-map / pullback — still **TODO** for
  predicates and ridge)?

  **Answers (theorem-backed):**

  * **D1.** There is a **vacuous** 𝒞 row on **`icNemsSpineCompressionCarrier`** (so **`Nonempty (S1LawfulFrontierRow _)`**),
    but **no** stratified outer with that exact outer spine (**`not_nonempty_stratified_vacuous_outer_on_icCarrier`**), so
    this row is **not** summit- / `𝔠`-compatible in the SPEC_009 sense.
  * **D2.** Any **`CertifiedFrontierRow`** on that carrier yields **`Nonempty (HFinal _)`**; by **`HFinal.nonempty_iff`**
    (via **`ic_phase1_nonempty_hfinal_iff_spine_data`**) this is **exactly** the **full spine + `(P,rcp)` + ridge +
    non-flat** checklist. The repository **does not** supply that checklist on the compression carrier today.
  * **D3 (represented).** The **earned** IC CS-3 **`AbsoluteFrontierRawS1`** slice on **`CorpusStrataCarrier`** is already
    packaged as **`certifiedFrontierRow_ic_cs3_aligned_nv`**; Stage D only **aliases** it under IC Stage D names.
  * **D4 (represented).** Same for **`SummitFE3SemanticPackage`** (**`icStageD_summitFE3_ic_cs3_aligned_nv`** + joint law).

  **Minimal compare witness + 𝒞 pullback (SPEC_031_ZK9 Stage A):** **`icStageD_constantCompareToCorpusBundle`** hosts
  **`icNativeCompressionLawfulArchitecture_cs3_pullback`** + **RawS1** corollaries in **`ICCompareRepresentationPullback`** —
  **ridge / `HFinal` / FE-3** pullback remains **TODO** (epic Stages B–D).

  **See also:** **`ICBridgeCoreRecord`** (corpus **`(P_IC,B_IC)`**), **`ICFe2TransportObstruction`** /
  **`ic_fe2_no_hfinal_from_layer_only`**, **`ICNativeOuterClosure`**, **`Lawful/ComparePullback`**.
-/

import AdequacyArchitecture.Burden.IrreducibleAdequacy
import AdequacyArchitecture.Instances.CorpusDischarge
import AdequacyArchitecture.Instances.ICBridgeCoreRecord
import AdequacyArchitecture.Instances.ICNativeOuterClosure
import AdequacyArchitecture.Lawful.FinalConditionalSummit
import AdequacyArchitecture.Lawful.LawfulStructures
import AdequacyArchitecture.Lawful.RidgeSummitStatements
import AdequacyArchitecture.Lawful.StratifiedLawfulArchitecture
import AdequacyArchitecture.Portability.CertifiedFrontierRow
import AdequacyArchitecture.Summit.UniversalIrreducibleAdequacy

universe u

namespace AdequacyArchitecture.Instances

open AdequacyArchitecture.Burden
open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open AdequacyArchitecture.Portability
open AdequacyArchitecture.Portability.BranchGenericSemanticTransport

/-! ## Vacuous 𝒞 row (any carrier) -/

variable (α : Type u)

/-- All adequacy modes false — maximum under-interpretation of “accounts” on `α`. -/
def icStageDVacuousOuterPred : AdequacyPredicates α where
  adeq := fun _ _ => False

/-- All burden modes false. -/
def icStageDVacuousOuterBurden : BurdenPredicates α where
  burden := fun _ _ => False

theorem icStageDVacuous_forces_each_mode (m : AdeqMode) :
    AdequacyForcesSomeBurden (icStageDVacuousOuterPred α) (icStageDVacuousOuterBurden α) m := by
  intro _ h
  cases h

/-- A **`LawfulAdequacyArchitecture`** that carries **no** realized adequacy (B1 is vacuous). -/
def icStageDVacuousLawful : LawfulAdequacyArchitecture α where
  P := icStageDVacuousOuterPred α
  B := icStageDVacuousOuterBurden α
  forces_each := icStageDVacuous_forces_each_mode α

theorem icStageD_not_nonempty_stratified_vacuous_outer :
    ¬ Nonempty { s : StratifiedLawfulAdequacyArchitecture α // s.outer = icStageDVacuousLawful α } := by
  rintro ⟨⟨_outer, bv⟩, hw⟩
  subst hw
  rcases bv with ⟨_m, ⟨_A, ⟨_A', hhold, _⟩⟩⟩
  simp [icStageDVacuousLawful, icStageDVacuousOuterBurden] at hhold

/-! ## D1 — native compression carrier: minimal S1 row + stratified obstruction -/

theorem icStageD_nonempty_s1LawfulFrontierRow_compressionCarrier :
    Nonempty (S1LawfulFrontierRow icNemsSpineCompressionCarrier) :=
  ⟨S1LawfulFrontierRow.ofLawful (icStageDVacuousLawful icNemsSpineCompressionCarrier)⟩

theorem icStageD_not_nonempty_stratified_vacuous_outer_on_compressionCarrier :
    ¬ Nonempty { s : StratifiedLawfulAdequacyArchitecture icNemsSpineCompressionCarrier //
        s.outer = icStageDVacuousLawful icNemsSpineCompressionCarrier } :=
  icStageD_not_nonempty_stratified_vacuous_outer icNemsSpineCompressionCarrier

/-! ## D2 — certified row ⇒ HFinal ⇒ spine checklist (native obstruction shape) -/

theorem icStageD_certifiedFrontierRow_compressionCarrier_implies_spine_checklist
    (h : Nonempty (CertifiedFrontierRow icNemsSpineCompressionCarrier)) :
    ∃ (𝔠 : CompletedStratifiedLawfulAdequacyArchitecture icNemsSpineCompressionCarrier)
      (P : AdequacyPredicates icNemsSpineCompressionCarrier)
      (rcp : RouteConstraintProfile icNemsSpineCompressionCarrier) (_ : RidgeCascadeWitness 𝔠)
      (_ : NonFlatFinalityFromRouteConstraintFor P rcp), True := by
  have hf : Nonempty (HFinal icNemsSpineCompressionCarrier) :=
    nonempty_certifiedFrontierRow_implies_nonempty_hfinal h
  exact ic_phase1_nonempty_hfinal_iff_spine_data.mp hf

/-! ## Minimal compare witness (representation morphism header only) -/

/-- Constant map to the first corpus stratum — **not** claimed to intertwine predicates or ridge data. -/
def icStageD_constantCompareToCorpusBundle : ICOuterClosureRepresentationCompare icNemsSpineCompressionCarrier where
  compareToCorpus := fun _ => ⟨0, by decide⟩

/-! ## D3 / D4 — represented IC CS-3 row (corpus carrier) -/

theorem icStageD_absoluteFrontierRawS1_ic_cs3_represented :
    AbsoluteFrontierRawS1 icCorpusAlignedNonVacuousFinalAdequacy icCorpusAlignedBurden :=
  absoluteFrontierRawS1_of_certifiedFrontierRow certifiedFrontierRow_ic_cs3_aligned_nv

def icStageD_summitFE3_ic_cs3_aligned_nv : SummitFE3SemanticPackage CorpusStrataCarrier :=
  CertifiedFrontierRow.toSummitFE3 certifiedFrontierRow_ic_cs3_aligned_nv

/-- **D4:** Stage-C joint law for the IC CS-3 represented **`SummitFE3SemanticPackage`**
(`summitFE3_joint_semantic_law` spelt out — proposition form, not the proof constant). -/
theorem icStageD_summitFE3_joint_ic_cs3 :
    MasterStratifiedAdequacyCascadeAt icStageD_summitFE3_ic_cs3_aligned_nv.summitTagged.toHFinal.𝔠
      icStageD_summitFE3_ic_cs3_aligned_nv.summitTagged.toHFinal.P
      icStageD_summitFE3_ic_cs3_aligned_nv.summitTagged.toHFinal.rcp ∧
      ForgetfulIndexedCoherent icStageD_summitFE3_ic_cs3_aligned_nv.fe3.ops ∧
        ForgetfulAgreementInjects icStageD_summitFE3_ic_cs3_aligned_nv.fe3.ops :=
  certifiedFrontierRow_summitFE3_joint certifiedFrontierRow_ic_cs3_aligned_nv

end AdequacyArchitecture.Instances
