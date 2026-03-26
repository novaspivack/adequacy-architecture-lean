/-
  **SPEC_030_MX7 — Stage A:** over-class **certified frontier row** interface and one-shot **RawS1** consequence.

  **Interface:** a **lawful** 𝒞 row (**`LawfulAdequacyArchitecture`**) together with a **role-tagged** summit
  witness (**`HFinalWithBranchRole`**) whose adequacy predicate **matches** the lawful **`P`**, plus **some**
  **`BranchGenericSemanticTransport.Core`** (FE-3 admissibility — trivial **`Unit`** core or nontrivial branch
  packaging).

  **Theorem:** **`AbsoluteFrontierRawS1`** for the lawful **`P`,`B`** pair via **`universal_irreducible_adequacy_lawful`**
  (summit + transport are **honest** common structure on earned rows; they do **not** strengthen the sufficiency
  proof — **Stage B** sharpens which hypotheses are essential).

  **Bool (FE-5 v2):** not yet an instance — no **`HFinal`** on the **`Bool`** carrier in this repository (see epic).

  **Stage B — hypothesis surface (SPEC_030):** **`S1LawfulFrontierRow`** =
  minimal **𝒞** packaging for the same **`AbsoluteFrontierRawS1`** conclusion (**`universal_irreducible_adequacy_lawful`**).
  **`CertifiedFrontierRow`** forgets to it via **`toS1Lawful`**; summit + **FE-3** are **provably irrelevant** to that
  conclusion (**`…_irrelevant_summit*`**, **`…_irrelevant_fe3`**).

  **Necessity (tightened):** explicit **`s1CounterexampleReprOnlyAdequacy` / `s1CounterexampleEmptyBurden`**
  (**`S1ShapeNecessityCounterexample.lean`**) refute **B1**, **𝒞**, **S1 shape**, and **`AbsoluteFrontierRawS1`**
  on **any** carrier; see also **`not_s1LawfulFrontierRow_counterexample_pair`**. **Stage C:** joint summit + FE-3 law
  (**`GenericSemanticSummitLift.lean`**, **`toSummitFE3`**).
-/

import AdequacyArchitecture.Portability.GenericSemanticSummitLift
import AdequacyArchitecture.Portability.S1ShapeNecessityCounterexample

import AdequacyArchitecture.Instances.CorpusLawfulRepresentation
import AdequacyArchitecture.Instances.ICSummitRepresentation
import AdequacyArchitecture.Instances.NEMSBridgeCoreRecord
import AdequacyArchitecture.Lawful.FinalConditionalSummit
import AdequacyArchitecture.Lawful.LawfulStructures
import AdequacyArchitecture.Lawful.MasterTheorem
import AdequacyArchitecture.Lawful.RelocationAlignedFinality
import AdequacyArchitecture.Portability.BranchGenericSemanticTransport
import AdequacyArchitecture.Summit.SummitBranchRoles
import AdequacyArchitecture.Summit.UniversalIrreducibleAdequacy
import AdequacyArchitecture.Toy.Fin2Model

universe u

namespace AdequacyArchitecture.Portability

open AdequacyArchitecture.Instances
open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open AdequacyArchitecture.Portability.BranchGenericSemanticTransport
open AdequacyArchitecture.Summit
open AdequacyArchitecture.Toy

variable {α : Type u}

/-- Canonical **`HFinal` on `Fin 2`** at **`toyPred`** with corridor **`bothFibersHoldRouteProfile`**. -/
def toyCorridorHFinal : HFinal (Fin 2) :=
  mkHFinal toyCompletedStratifiedLawfulAdequacyArchitecture toyPred bothFibersHoldRouteProfile
    toy_ridgeCascadeWitness (toy_nonFlatFinalityFor_toyPred bothFibersHoldRouteProfile)

/--
**SPEC_030_MX7 — certified frontier row** (over-class hypothesis bundle above the FE-4 ladder).

* **`lawful`:** 𝒞 row carrying the **`P`,`B`** pair for the target **S1** / **`AbsoluteFrontierRawS1`** conclusion.
* **`summitTagged`:** **Layer A** summit witness + **SPEC_026/030** branch-role tag (`relocationFinality` on corpus rows;
  **`certificationRepresentation`** / **`compositionGluing`** also admissible — see **`SummitBranchRoles`**).
* **`summit_lawful_sameAdequacy`:** the summit predicate agrees with **`lawful.P`** (corridor / packaging can use a **different** outer-spine burden than **`lawful.B`** — see NEMS **`relocDemoBurden`** vs toy outer **`B`**).
* **`fe3`:** an admissible **FE-3** `Core` witness (here packaged as the **trivial** `Unit` core — always valid;
  branch **nontrivial** `Core`s are **additional** certifying data, e.g. **`NEMSBranchGenericSemanticTransport`**).
  **Stage B:** for the **S1** conclusion, **`fe3`** and the summit fields are **proof-irrelevant** (**`…_irrelevant_*`** below).
-/
structure CertifiedFrontierRow (α : Type u) where
  lawful : LawfulAdequacyArchitecture α
  summitTagged : HFinalWithBranchRole α
  summit_lawful_sameAdequacy : summitTagged.toHFinal.P = lawful.P
  fe3 : Fe3UnitCore

/-- Certified packaging **implies** **`Nonempty (HFinal α)`** — common **D–E** obstruction step. -/
theorem nonempty_certifiedFrontierRow_implies_nonempty_hfinal {β : Type u} :
    Nonempty (CertifiedFrontierRow β) → Nonempty (HFinal β) := by
  rintro ⟨row⟩
  exact ⟨row.summitTagged.toHFinal⟩

/--
**Over-class theorem (Stage A):** every **`CertifiedFrontierRow`** inherits **`AbsoluteFrontierRawS1`** for its lawful predicates.

**Proof:** **`MasterTheorem.universal_irreducible_adequacy_lawful`** on **`lawful`** alone.
-/
theorem absoluteFrontierRawS1_of_certifiedFrontierRow (row : CertifiedFrontierRow α) :
    AbsoluteFrontierRawS1 row.lawful.P row.lawful.B :=
  universal_irreducible_adequacy_lawful row.lawful

/-! ## Stage B (SPEC_030) — minimal 𝒞 gate, forgetful map, irrelevance -/

/--
**Minimal hypothesis** for the **proved** RawS1 / Layer-B name on earned rows: a single **`LawfulAdequacyArchitecture`**
(SPEC_008 𝒞). Every **`absoluteFrontierRawS1_of_certifiedFrontierRow`** proof factors through **`toS1Lawful`**.
-/
structure S1LawfulFrontierRow (α : Type u) where
  lawful : LawfulAdequacyArchitecture α

/-- Wrap a **`LawfulAdequacyArchitecture`** as the **Stage B** minimal row. -/
abbrev S1LawfulFrontierRow.ofLawful (𝔸 : LawfulAdequacyArchitecture α) : S1LawfulFrontierRow α :=
  ⟨𝔸⟩

/-- **`AbsoluteFrontierRawS1`** from the minimal row — **defeq** to **`universal_irreducible_adequacy_lawful`**. -/
theorem absoluteFrontierRawS1_of_s1LawfulFrontierRow (row : S1LawfulFrontierRow α) :
    AbsoluteFrontierRawS1 row.lawful.P row.lawful.B :=
  universal_irreducible_adequacy_lawful row.lawful

theorem absoluteFrontierRawS1_of_s1LawfulFrontierRow_eq_universal_irreducible
    (row : S1LawfulFrontierRow α) :
    absoluteFrontierRawS1_of_s1LawfulFrontierRow row = universal_irreducible_adequacy_lawful row.lawful :=
  rfl

/-- Forget certified packaging; keep only the lawful spine. -/
def CertifiedFrontierRow.toS1Lawful (row : CertifiedFrontierRow α) : S1LawfulFrontierRow α :=
  ⟨row.lawful⟩

/--
**Factorization:** the certified-row theorem is **definitionally** the minimal theorem on **`row.lawful`**.
-/
theorem absoluteFrontierRawS1_of_certifiedFrontierRow_eq_s1Lawful (row : CertifiedFrontierRow α) :
    absoluteFrontierRawS1_of_certifiedFrontierRow row =
      absoluteFrontierRawS1_of_s1LawfulFrontierRow row.toS1Lawful :=
  rfl

/--
**FE-3 irrelevance:** replacing **`fe3`** does not change the proved **`AbsoluteFrontierRawS1`** statement **(the proof never
uses `fe3`)**.
-/
theorem absoluteFrontierRawS1_of_certifiedFrontierRow_irrelevant_fe3
    (lawful : LawfulAdequacyArchitecture α) (summitTagged : HFinalWithBranchRole α)
    (h : summitTagged.toHFinal.P = lawful.P) (c₁ c₂ : Fe3UnitCore) :
    absoluteFrontierRawS1_of_certifiedFrontierRow ⟨lawful, summitTagged, h, c₁⟩ =
      absoluteFrontierRawS1_of_certifiedFrontierRow ⟨lawful, summitTagged, h, c₂⟩ :=
  rfl

/--
**Summit irrelevance** at fixed **`lawful`:** any compatible **`HFinalWithBranchRole`** (same **`P`**) yields the same proof.
-/
theorem absoluteFrontierRawS1_of_certifiedFrontierRow_irrelevant_summitTagged
    (lawful : LawfulAdequacyArchitecture α)
    (s₁ s₂ : HFinalWithBranchRole α) (h₁ : s₁.toHFinal.P = lawful.P) (h₂ : s₂.toHFinal.P = lawful.P)
    (c : Fe3UnitCore) :
    absoluteFrontierRawS1_of_certifiedFrontierRow ⟨lawful, s₁, h₁, c⟩ =
      absoluteFrontierRawS1_of_certifiedFrontierRow ⟨lawful, s₂, h₂, c⟩ :=
  rfl

/-- Sum lawful + aligned summit, default **`fe3 := fe3TrivialUnitCore`**. -/
def certifiedFrontierRow_of_lawful_summitAligned (lawful : LawfulAdequacyArchitecture α)
    (summitTagged : HFinalWithBranchRole α) (h : summitTagged.toHFinal.P = lawful.P) : CertifiedFrontierRow α :=
  ⟨lawful, summitTagged, h, fe3TrivialUnitCore⟩

theorem absoluteFrontierRawS1_certifiedFrontierRow_of_lawful_summitAligned
    (lawful : LawfulAdequacyArchitecture α)
    (summitTagged : HFinalWithBranchRole α) (h : summitTagged.toHFinal.P = lawful.P) :
    absoluteFrontierRawS1_of_certifiedFrontierRow
        (certifiedFrontierRow_of_lawful_summitAligned lawful summitTagged h) =
      absoluteFrontierRawS1_of_s1LawfulFrontierRow ⟨lawful⟩ :=
  rfl

/-! ## Stage C (SPEC_030) — `SummitFE3SemanticPackage` / joint law -/

/-- Drop lawful data; keep summit + **FE-3** (branch-generic semantic package). -/
def CertifiedFrontierRow.toSummitFE3 (row : CertifiedFrontierRow α) : SummitFE3SemanticPackage α :=
  ⟨row.summitTagged, row.fe3⟩

theorem certifiedFrontierRow_summitFE3_joint (row : CertifiedFrontierRow α) :
    MasterStratifiedAdequacyCascadeAt row.summitTagged.toHFinal.𝔠 row.summitTagged.toHFinal.P
        row.summitTagged.toHFinal.rcp ∧
      ForgetfulIndexedCoherent row.fe3.ops ∧ ForgetfulAgreementInjects row.fe3.ops :=
  summitFE3_joint_semantic_law row.toSummitFE3

theorem not_s1LawfulFrontierRow_counterexample_pair (row : S1LawfulFrontierRow α)
    (hP : row.lawful.P = s1CounterexampleReprOnlyAdequacy α)
    (hB : row.lawful.B = s1CounterexampleEmptyBurden α) : False :=
  not_lawfulAdequacyArchitecture_eq_reprOnly_emptyBurden row.lawful hP hB

/-! ## Instances — FE-4 earned rows (SPEC_029) -/

def certifiedFrontierRow_toy_fin2 : CertifiedFrontierRow (Fin 2) where
  lawful := toyLawfulArchitecture
  summitTagged := HFinalWithBranchRole.ofRelocationFinality toyCorridorHFinal
  summit_lawful_sameAdequacy := rfl
  fe3 := fe3TrivialUnitCore

def certifiedFrontierRow_corpus_toy_spine : CertifiedFrontierRow CorpusStrataCarrier where
  lawful := corpusToyLawfulArchitecture
  summitTagged := HFinalWithBranchRole.ofRelocationFinality corpusNemsFin2HFinal
  summit_lawful_sameAdequacy := rfl
  fe3 := fe3TrivialUnitCore

def certifiedFrontierRow_corpus_nems_level1 : CertifiedFrontierRow CorpusStrataCarrier where
  lawful := corpusNemsFin2LawfulArchitecture
  summitTagged := HFinalWithBranchRole.ofRelocationFinality corpusNemsFin2HFinal
  summit_lawful_sameAdequacy := rfl
  fe3 := fe3TrivialUnitCore

def certifiedFrontierRow_corpus_nems_level2_nv : CertifiedFrontierRow CorpusStrataCarrier where
  lawful := corpusNemsFin2NvLawfulArchitecture
  summitTagged := HFinalWithBranchRole.ofRelocationFinality icCS3HFinal
  summit_lawful_sameAdequacy := rfl
  fe3 := fe3TrivialUnitCore

/-- **IC CS-3** aligned naming — same certified row as **Level 2 NV** (`icCorpusAligned*` abbrev). -/
abbrev certifiedFrontierRow_ic_cs3_aligned_nv := certifiedFrontierRow_corpus_nems_level2_nv

theorem certifiedFrontierRow_toy_fin2_eq_mk :
    certifiedFrontierRow_toy_fin2 =
      certifiedFrontierRow_of_lawful_summitAligned toyLawfulArchitecture
        (HFinalWithBranchRole.ofRelocationFinality toyCorridorHFinal) rfl :=
  rfl

theorem certifiedFrontierRow_corpus_toy_spine_eq_mk :
    certifiedFrontierRow_corpus_toy_spine =
      certifiedFrontierRow_of_lawful_summitAligned corpusToyLawfulArchitecture
        (HFinalWithBranchRole.ofRelocationFinality corpusNemsFin2HFinal) rfl :=
  rfl

theorem certifiedFrontierRow_corpus_nems_level1_eq_mk :
    certifiedFrontierRow_corpus_nems_level1 =
      certifiedFrontierRow_of_lawful_summitAligned corpusNemsFin2LawfulArchitecture
        (HFinalWithBranchRole.ofRelocationFinality corpusNemsFin2HFinal) rfl :=
  rfl

theorem certifiedFrontierRow_corpus_nems_level2_nv_eq_mk :
    certifiedFrontierRow_corpus_nems_level2_nv =
      certifiedFrontierRow_of_lawful_summitAligned corpusNemsFin2NvLawfulArchitecture
        (HFinalWithBranchRole.ofRelocationFinality icCS3HFinal) rfl :=
  rfl

/-! ## Bridges — same conclusion as **`AbsoluteFrontierEarnedToy`** `fe4_*` via the over-class theorem -/

theorem fe4_earned_absoluteFrontierRawS1_fin2_toy_via_certifiedRow :
    AbsoluteFrontierRawS1 toyPred toyBurden :=
  absoluteFrontierRawS1_of_certifiedFrontierRow certifiedFrontierRow_toy_fin2

theorem fe4_earned_absoluteFrontierRawS1_corpus_summit_lawful_spine_via_certifiedRow :
    AbsoluteFrontierRawS1 corpusToyLawfulArchitecture.P corpusToyLawfulArchitecture.B :=
  absoluteFrontierRawS1_of_certifiedFrontierRow certifiedFrontierRow_corpus_toy_spine

theorem fe4_earned_absoluteFrontierRawS1_corpus_nems_corridor_level1_via_certifiedRow :
    AbsoluteFrontierRawS1 corpusNemsFin2Adequacy corpusNemsFin2Burden :=
  absoluteFrontierRawS1_of_certifiedFrontierRow certifiedFrontierRow_corpus_nems_level1

theorem fe4_earned_absoluteFrontierRawS1_corpus_nems_corridor_level2_nv_via_certifiedRow :
    AbsoluteFrontierRawS1 corpusNemsFin2NonVacuousFinalAdequacy corpusNemsFin2Burden :=
  absoluteFrontierRawS1_of_certifiedFrontierRow certifiedFrontierRow_corpus_nems_level2_nv

theorem fe4_earned_absoluteFrontierRawS1_ic_cs3_aligned_nv_via_certifiedRow :
    AbsoluteFrontierRawS1 icCorpusAlignedNonVacuousFinalAdequacy icCorpusAlignedBurden :=
  absoluteFrontierRawS1_of_certifiedFrontierRow certifiedFrontierRow_ic_cs3_aligned_nv

end AdequacyArchitecture.Portability
