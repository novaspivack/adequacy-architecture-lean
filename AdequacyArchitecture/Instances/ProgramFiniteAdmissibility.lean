/-
  **SPEC_036_FA1** — finite admissibility **`G_adm`** (successor charter; Program 1 tranche frozen).

  **S-1:** `program1FiniteGAdm γ` := **`Nonempty (Program1FiniteGAdm γ)`** — a **finite** witness family; any witness
  yields **`∃ P B, AbsoluteFrontierRawS1 P B`** (`exists_absoluteFrontierRawS1_of_program1FiniteGAdm`).

  **Witness constructors:**
  * **`pullback`** — `Program1AdmissibilityPullbackDisplayWitness` (`U_pullback` / S1a API), including **S3b** **`Q₁`**
    via **`program1_icCs3CompareQuotientRepr_isPullbackDisplay`** and **Fin 2** corpus **NEMS** displays.
  * **`icStageDFullPack`** — `γ = icNemsSpineCompressionCarrier` plus **four** **`PLift`** fields matching the projection
    structure of **`icSpec031_stageD_resolution_pack`** in **`ICCompareRepresentationPullback`**: **iff** spine (`.1`),
    **RawS1** (`.2.1`), **bypass** (`.2.2.1`), **cascade** (`.2.2.2`).
  * **`upgradeWitness`** — **`CertifiedUpgradeWitness γ`** (**S2d**): certified row packaging ⇒ **`AbsoluteFrontierRawS1`**
    for **`w.base.arch`** (**`absoluteFrontierRawS1_of_certifiedUpgradeWitness`**).

  **S5 note:** lemmas such as **`pullbackDisplay_with_host_summitFE3_*`** strengthen a **pullback** witness with a **parallel**
  host **summitFE3** joint — **not** part of the **`G_adm`** **consequence** (**`AbsoluteFrontierRawS1`** only).

  **FA1-NQ1 (`Q₂`):** **`corpusStrataCoarseQuotient`** — **host-coarse** **`Quot`** of **`CorpusStrataCarrier`**; **`G_adm`** via **`pullback`** (**`program1FiniteGAdm_corpusStrataCoarseQuotient`**).

  **FA1-NQ12 (`Q₃`):** **`fin3ParityQuotient`** — **parity** **`Quot`** on **`Fin 3`** (**intermediate**); **`G_adm`** via **`pullback`** (**`program1FiniteGAdm_fin3ParityQuotient`**).

  **Flagship package (NQ10):** **`program1FiniteGAdm_implies_exists_absoluteFrontierRawS1`** (+ **`…_ofWitness`**) — **canonical** consequence statement.

  **Work queue:** `specs/IN-PROCESS/SPEC_036_FA1/SPEC_036_FA1_WORK_QUEUE.md`.

  **SPEC_037_MU1:** **`program1FiniteGAdm γ` ↔ `Program1AdmissibilityPullbackDisplayWitness γ`** — see **`Program1MetaUnificationMU1.lean`**.
-/

import AdequacyArchitecture.Instances.CorpusStrataCoarseQuotient
import AdequacyArchitecture.Instances.Fin3ParityQuotient
import AdequacyArchitecture.Instances.ICCompareRepresentationPullback
import AdequacyArchitecture.Lawful.FinalConditionalSummit
import AdequacyArchitecture.Lawful.RidgeBridgeable
import AdequacyArchitecture.Portability.RepresentationCalculusMX7
import AdequacyArchitecture.Portability.SummitRowRepresentation

namespace AdequacyArchitecture.Instances

open AdequacyArchitecture.AbsoluteFrontier
open AdequacyArchitecture.Burden
open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open AdequacyArchitecture.Portability

/-- **`U_pullback`-style witness:** ∃ host, compare representation, and displayed `(P,B)` (S1a / SPEC_035 Q1 API). -/
def Program1AdmissibilityPullbackDisplayWitness (γ : Type) : Prop :=
  ∃ (α : Type) (repr : CertifiedFrontierRepresentation γ α) (P : AdequacyPredicates γ)
    (B : BurdenPredicates γ), repr.IsPullbackDisplay P B

/-- **IC Stage D — iff spine** conjunct (matches **`icSpec031_stageD_resolution_pack.1`**). -/
abbrev icSpec031_stageD_iff_conjunct : Prop :=
  (Nonempty (HFinal icNemsSpineCompressionCarrier) ↔
      ∃ (𝔠 : CompletedStratifiedLawfulAdequacyArchitecture icNemsSpineCompressionCarrier)
        (P : AdequacyPredicates icNemsSpineCompressionCarrier)
        (rcp : RouteConstraintProfile icNemsSpineCompressionCarrier) (_ : RidgeCascadeWitness 𝔠)
        (_ : NonFlatFinalityFromRouteConstraintFor P rcp), True)

/-- IC flagship **RawS1** slice (**`icSpec031`**, same type as **`icSpec031_stageD_resolution_pack.2.1`**). -/
abbrev icSpec031_stageD_absoluteFrontierRawS1_conjunct : Prop :=
  AbsoluteFrontierRawS1 icNativeCompressionLawfulArchitecture_cs3_pullback.P
    icNativeCompressionLawfulArchitecture_cs3_pullback.B

/-- **Bypass** conjunct (**`icSpec031_stageD_resolution_pack.2.2.1`**). -/
abbrev icSpec031_stageD_bypass_conjunct : Prop :=
  Nonempty ICSummitContractBypassWitness

/-- **Layer-A cascade** on **`icCS3HFinal`** (**`icSpec031_stageD_resolution_pack.2.2.2`**). -/
abbrev icSpec031_stageD_cascade_conjunct : Prop :=
  MasterStratifiedAdequacyCascadeAt icCS3HFinal.𝔠 icCS3HFinal.P icCS3HFinal.rcp

/-! ## SPEC_043_SR1 — reconstruction hooks (Stage D facets from named lemmas) -/

/-- **SR1-F1** — AF-1 sharp iff on the IC spine carrier (**same** **Prop** **as** **`icSpec031_stageD_iff_conjunct`**). -/
theorem icSpec031_stageD_iff_conjunct_of_af1_native_carrier :
    icSpec031_stageD_iff_conjunct :=
  af1_icNativeCarrier_nonempty_hfinal_iff_spine

/-- **SR1-F3** — theorem-fed without the full Stage D **`∧`** (standard bypass witness). -/
theorem icSpec031_stageD_bypass_conjunct_of_af1_standard : icSpec031_stageD_bypass_conjunct :=
  af1_standard_bypass_nonempty

/-- **SR1-F4** — cascade at **`icCS3HFinal`** without assuming **F3** as hypothesis. -/
theorem icSpec031_stageD_cascade_conjunct_of_af1_standard : icSpec031_stageD_cascade_conjunct :=
  af1_standard_bypass_yields_highest_summit

/--
Boxes the **IC Stage D** pack as **`Type`**-level data via **four** **`PLift`** fields aligned to **`icSpec031`** projections.
-/
structure Program1IcStageDFullPackWitness where
  iff_lift : PLift icSpec031_stageD_iff_conjunct
  raw_lift : PLift icSpec031_stageD_absoluteFrontierRawS1_conjunct
  bypass_lift : PLift icSpec031_stageD_bypass_conjunct
  cascade_lift : PLift icSpec031_stageD_cascade_conjunct

/-- **`Type 2`:** **`CertifiedUpgradeWitness γ`** lives one universe higher than **`Type 0`** carriers. -/
inductive Program1FiniteGAdm (γ : Type) : Type 2 where
  /-- Compare-pullback display witness (S1a / `U_pullback`). -/
  | pullback : Program1AdmissibilityPullbackDisplayWitness γ → Program1FiniteGAdm γ
  /-- Flagship IC carrier + **full** Stage D pack witness (`U_cert_pack`, **hardened**). -/
  | icStageDFullPack : γ = icNemsSpineCompressionCarrier → Program1IcStageDFullPackWitness → Program1FiniteGAdm γ
  /-- **S2d** — certified upgrade ⇒ RawS1 for **`base.arch`**. -/
  | upgradeWitness : CertifiedUpgradeWitness γ → Program1FiniteGAdm γ

/-- **`G_adm` membership** (SPEC_036_FA1): **some** finite-admissibility witness. -/
abbrev program1FiniteGAdm (γ : Type) : Prop :=
  Nonempty (Program1FiniteGAdm γ)

theorem exists_absoluteFrontierRawS1_of_program1Admissibility_pullbackDisplayWitness
    {γ : Type} (h : Program1AdmissibilityPullbackDisplayWitness γ) :
    ∃ (P : AdequacyPredicates γ) (B : BurdenPredicates γ), AbsoluteFrontierRawS1 P B := by
  rcases h with ⟨_α, repr, P, B, hd⟩
  exact ⟨P, B, absoluteFrontierRawS1_of_valid_certifiedFrontierRepresentation repr hd⟩

theorem exists_absoluteFrontierRawS1_of_program1FiniteGAdm {γ : Type} (h : program1FiniteGAdm γ) :
    ∃ (P : AdequacyPredicates γ) (B : BurdenPredicates γ), AbsoluteFrontierRawS1 P B := by
  rcases h with ⟨w⟩
  match w with
  | Program1FiniteGAdm.pullback hpb =>
    exact exists_absoluteFrontierRawS1_of_program1Admissibility_pullbackDisplayWitness hpb
  | Program1FiniteGAdm.icStageDFullPack he ⟨PLift.up _, PLift.up hr, _, _⟩ =>
    subst he
    refine ⟨icNativeCompressionLawfulArchitecture_cs3_pullback.P,
        icNativeCompressionLawfulArchitecture_cs3_pullback.B, ?_⟩
    exact hr
  | Program1FiniteGAdm.upgradeWitness w =>
    refine ⟨w.base.arch.P, w.base.arch.B, absoluteFrontierRawS1_of_certifiedUpgradeWitness w⟩

/-- **FA1-NQ10:** **canonical** **flagship** **consequence** — **`G_adm` ⇒ ∃ raw S1** (alias for naming stability). -/
theorem program1FiniteGAdm_implies_exists_absoluteFrontierRawS1 {γ : Type} (h : program1FiniteGAdm γ) :
    ∃ (P : AdequacyPredicates γ) (B : BurdenPredicates γ), AbsoluteFrontierRawS1 P B :=
  exists_absoluteFrontierRawS1_of_program1FiniteGAdm h

/--
**FA1-NQ10:** same conclusion unpacked from an explicit **witness** (**case-analysis** **head** matches **constructors**).
-/
theorem program1FiniteGAdm_implies_exists_absoluteFrontierRawS1_ofWitness {γ : Type} (w : Program1FiniteGAdm γ) :
    ∃ (P : AdequacyPredicates γ) (B : BurdenPredicates γ), AbsoluteFrontierRawS1 P B :=
  exists_absoluteFrontierRawS1_of_program1FiniteGAdm ⟨w⟩

/-! ## Named **`pullback`** witnesses (matrix / reduction map) -/

/-- **S3b **`Q₁`**** — compare-quotient carrier (**`ICCompareRepresentationPullback`**). -/
theorem program1_program1AdmissibilityPullbackDisplayWitness_icCs3CompareQuotient :
    Program1AdmissibilityPullbackDisplayWitness program1_icCs3CompareQuotient :=
  ⟨CorpusStrataCarrier, program1_icCs3CompareQuotientRepr,
    program1_icCs3CompareQuotient_pullbackLawful.P,
    program1_icCs3CompareQuotient_pullbackLawful.B,
    program1_icCs3CompareQuotientRepr_isPullbackDisplay⟩

/-- **S1a — one-step IC CS-3** compare representation on **`icNemsSpineCompressionCarrier`** (**`ICCompareRepresentationPullback`**). -/
theorem program1_program1AdmissibilityPullbackDisplayWitness_icCs3SpineCompression :
    Program1AdmissibilityPullbackDisplayWitness icNemsSpineCompressionCarrier :=
  ⟨CorpusStrataCarrier, icCs3CertifiedFrontierRepresentation,
    icNativeCompressionLawfulArchitecture_cs3_pullback.P,
    icNativeCompressionLawfulArchitecture_cs3_pullback.B,
    icCs3CertifiedFrontierRepresentation_isPullbackDisplay⟩

/-- **S1a+ — composed** **`comp (corpus NV swap) icCs3`** tower (**same** native **`P,B`** as one-step **IC CS-3**). -/
theorem program1_program1AdmissibilityPullbackDisplayWitness_icCs3CompCorpusNvSwap :
    Program1AdmissibilityPullbackDisplayWitness icNemsSpineCompressionCarrier :=
  ⟨CorpusStrataCarrier, icCs3CompCorpusNvSwapCertifiedFrontierRepresentation,
    icNativeCompressionLawfulArchitecture_cs3_pullback.P,
    icNativeCompressionLawfulArchitecture_cs3_pullback.B,
    icCs3CompCorpusNvSwapCertifiedFrontierRepresentation_isPullbackDisplay⟩

/-- **Corpus NEMS Level-1** (**Fin 2**, **`π = id`**) — **`SummitRowRepresentation`**. -/
theorem program1_program1AdmissibilityPullbackDisplayWitness_corpusNemsFin2Level1Id :
    Program1AdmissibilityPullbackDisplayWitness CorpusStrataCarrier :=
  ⟨CorpusStrataCarrier, certifiedFrontierRepresentation_corpus_nems_level1_id,
    corpusNemsFin2Adequacy, corpusNemsFin2Burden,
    certifiedFrontierRepresentation_corpus_nems_level1_id_isPullbackDisplay⟩

/-- **Corpus NEMS Level-2 NV** (`π = id`). -/
theorem program1_program1AdmissibilityPullbackDisplayWitness_corpusNemsFin2Level2NvId :
    Program1AdmissibilityPullbackDisplayWitness CorpusStrataCarrier :=
  ⟨CorpusStrataCarrier, certifiedFrontierRepresentation_corpus_nems_level2_nv_id,
    icCorpusAlignedNonVacuousFinalAdequacy, icCorpusAlignedBurden,
    certifiedFrontierRepresentation_corpus_nems_level2_nv_id_isPullbackDisplay⟩

/-- **Corpus NEMS Level-2 NV** (**fiber swap** compare). -/
theorem program1_program1AdmissibilityPullbackDisplayWitness_corpusNemsFin2Level2NvSwap :
    Program1AdmissibilityPullbackDisplayWitness CorpusStrataCarrier :=
  ⟨CorpusStrataCarrier, certifiedFrontierRepresentation_corpus_nems_level2_nv_swap,
    icCorpusAlignedNonVacuousFinalAdequacy, icCorpusAlignedBurden,
    certifiedFrontierRepresentation_corpus_nems_level2_nv_swap_isPullbackDisplay⟩

/-- **S3b — `Q₂` canary:** **host-coarse** quotient of **`CorpusStrataCarrier`** (**FA1-NQ1** — not an IC compare kernel). -/
theorem program1_program1AdmissibilityPullbackDisplayWitness_corpusStrataCoarseQuotient :
    Program1AdmissibilityPullbackDisplayWitness corpusStrataCoarseQuotient :=
  ⟨CorpusStrataCarrier, corpusStrataCoarseQuotientRepr,
    corpusStrataCoarseQuotient_pullbackLawful.P,
    corpusStrataCoarseQuotient_pullbackLawful.B,
    corpusStrataCoarseQuotientRepr_isPullbackDisplay⟩

/-- **S3b — `Q₃` canary:** **parity** quotient of **`Fin 3`** (**FA1-NQ12** — **intermediate**, **nontrivial** classes). -/
theorem program1_program1AdmissibilityPullbackDisplayWitness_fin3ParityQuotient :
    Program1AdmissibilityPullbackDisplayWitness fin3ParityQuotient :=
  ⟨CorpusStrataCarrier, fin3ParityQuotientRepr,
    fin3ParityQuotient_pullbackLawful.P,
    fin3ParityQuotient_pullbackLawful.B,
    fin3ParityQuotientRepr_isPullbackDisplay⟩

/-- Default IC witness from the proved **`icSpec031`** pack (**hardened** facets). -/
def program1FiniteGAdm_witness_icNems_default : Program1FiniteGAdm icNemsSpineCompressionCarrier :=
  Program1FiniteGAdm.icStageDFullPack rfl
    { iff_lift := PLift.up icSpec031_stageD_resolution_pack.1
      raw_lift := PLift.up icSpec031_stageD_resolution_pack.2.1
      bypass_lift := PLift.up icSpec031_stageD_resolution_pack.2.2.1
      cascade_lift := PLift.up icSpec031_stageD_resolution_pack.2.2.2 }

theorem program1FiniteGAdm_icNems : program1FiniteGAdm icNemsSpineCompressionCarrier :=
  Nonempty.intro program1FiniteGAdm_witness_icNems_default

/-- Alternate **`G_adm`** membership for the IC spine carrier via **display** (**`U_pullback`**) instead of **`icStageDFullPack`. -/
def program1FiniteGAdm_witness_icNems_via_icCs3_pullback : Program1FiniteGAdm icNemsSpineCompressionCarrier :=
  Program1FiniteGAdm.pullback program1_program1AdmissibilityPullbackDisplayWitness_icCs3SpineCompression

theorem program1FiniteGAdm_icNems_via_icCs3_pullback :
    program1FiniteGAdm icNemsSpineCompressionCarrier :=
  Nonempty.intro program1FiniteGAdm_witness_icNems_via_icCs3_pullback

/-- **`G_adm`** / **S1a+** — **swap ∘ compare** tower on the IC spine carrier (**same** **`P,B`** as **`icCs3`** one-step). -/
def program1FiniteGAdm_witness_icNems_via_icCs3CompCorpusNvSwap_pullback :
    Program1FiniteGAdm icNemsSpineCompressionCarrier :=
  Program1FiniteGAdm.pullback program1_program1AdmissibilityPullbackDisplayWitness_icCs3CompCorpusNvSwap

theorem program1FiniteGAdm_icNems_via_icCs3CompCorpusNvSwap_pullback :
    program1FiniteGAdm icNemsSpineCompressionCarrier :=
  Nonempty.intro program1FiniteGAdm_witness_icNems_via_icCs3CompCorpusNvSwap_pullback

/-! ## **S5** — parallel **`pullbackDisplay_with_host_summitFE3`** (re-export spine for **036** citations) -/

/-- **S5** packaging for **IC CS-3** — **not** part of **`G_adm`** membership; **parallel** to **`program1_program1AdmissibilityPullbackDisplayWitness_icCs3SpineCompression`**. -/
abbrev program1_icCs3_pullbackDisplay_with_host_summitFE3 :=
  icCs3PullbackDisplay_with_host_summitFE3

/-- **S5** for **`comp (swap NV) icCs3`** — **parallel** to **`program1_program1AdmissibilityPullbackDisplayWitness_icCs3CompCorpusNvSwap`**. -/
abbrev program1_icCs3CompCorpusNvSwap_pullbackDisplay_with_host_summitFE3 :=
  icCs3CompCorpusNvSwapPullbackDisplay_with_host_summitFE3

/-- **S5** for **`Q₁`** compare kernel — alias for **`program1_icCs3CompareQuotient_pullbackDisplay_with_host_summitFE3`** (**`ICCompareRepresentationPullback`**). -/
abbrev program1_Q1_pullbackDisplay_with_host_summitFE3 :=
  program1_icCs3CompareQuotient_pullbackDisplay_with_host_summitFE3

/-- **S5** for **`Q₂`** coarse **Fin 2** quotient — alias for **`corpusStrataCoarseQuotient_pullbackDisplay_with_host_summitFE3`**. -/
abbrev program1_Q2_pullbackDisplay_with_host_summitFE3 :=
  corpusStrataCoarseQuotient_pullbackDisplay_with_host_summitFE3

/-- **S5** for **`Q₃`** **Fin 3** **parity** quotient. -/
abbrev program1_Q3_pullbackDisplay_with_host_summitFE3 :=
  fin3ParityQuotient_pullbackDisplay_with_host_summitFE3

def program1FiniteGAdm_witness_icCs3CompareQuotient_default :
    Program1FiniteGAdm program1_icCs3CompareQuotient :=
  Program1FiniteGAdm.pullback program1_program1AdmissibilityPullbackDisplayWitness_icCs3CompareQuotient

theorem program1FiniteGAdm_icCs3CompareQuotient :
    program1FiniteGAdm program1_icCs3CompareQuotient :=
  Nonempty.intro program1FiniteGAdm_witness_icCs3CompareQuotient_default

def program1FiniteGAdm_witness_corpusStrataCoarseQuotient_default :
    Program1FiniteGAdm corpusStrataCoarseQuotient :=
  Program1FiniteGAdm.pullback program1_program1AdmissibilityPullbackDisplayWitness_corpusStrataCoarseQuotient

theorem program1FiniteGAdm_corpusStrataCoarseQuotient :
    program1FiniteGAdm corpusStrataCoarseQuotient :=
  Nonempty.intro program1FiniteGAdm_witness_corpusStrataCoarseQuotient_default

def program1FiniteGAdm_witness_fin3ParityQuotient_default :
    Program1FiniteGAdm fin3ParityQuotient :=
  Program1FiniteGAdm.pullback program1_program1AdmissibilityPullbackDisplayWitness_fin3ParityQuotient

theorem program1FiniteGAdm_fin3ParityQuotient :
    program1FiniteGAdm fin3ParityQuotient :=
  Nonempty.intro program1FiniteGAdm_witness_fin3ParityQuotient_default

theorem program1FiniteGAdm_corpusStrata_via_level1_id :
    program1FiniteGAdm CorpusStrataCarrier :=
  Nonempty.intro
    (Program1FiniteGAdm.pullback program1_program1AdmissibilityPullbackDisplayWitness_corpusNemsFin2Level1Id)

theorem program1FiniteGAdm_corpusStrata_via_level2_nv_id :
    program1FiniteGAdm CorpusStrataCarrier :=
  Nonempty.intro
    (Program1FiniteGAdm.pullback program1_program1AdmissibilityPullbackDisplayWitness_corpusNemsFin2Level2NvId)

theorem program1FiniteGAdm_corpusStrata_via_level2_nv_swap :
    program1FiniteGAdm CorpusStrataCarrier :=
  Nonempty.intro
    (Program1FiniteGAdm.pullback program1_program1AdmissibilityPullbackDisplayWitness_corpusNemsFin2Level2NvSwap)

theorem program1FiniteGAdm_of_certifiedUpgradeWitness {γ : Type} (w : CertifiedUpgradeWitness γ) :
    program1FiniteGAdm γ :=
  Nonempty.intro (Program1FiniteGAdm.upgradeWitness w)

end AdequacyArchitecture.Instances
