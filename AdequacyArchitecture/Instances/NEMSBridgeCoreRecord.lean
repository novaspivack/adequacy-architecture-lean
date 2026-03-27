/-
  **SPEC_024 — NEMS branch: bridge-core instantiation record** (first honest packaging).

  **SPEC_013 NEMS row (`CorpusStrataCarrier = Fin 2`):** the program maps the shared corpus carrier to the
  earned toy spine; we record an explicit `(B, P, rcp)` satisfying the **minimal proof-essential bridge**
  (`UniversalBurdenRelocationLawfulAtBurden`, `FinalAccountsParticipateInRelocation`,
  `LawfulRouteForcesRcpInhonesty`) plus **`NonFlatFinalityFromRouteConstraintFor`**.

  Two corridor rows (see `SPEC_024_NM1` level taxonomy):

  * **Level 1 (typed):** `corpusNemsFin2Adequacy` = `toyPred` — final participation **vacuous** (`toyPred_no_final_adequacy`).
  * **Level 2 (non-vacuous finality):** `corpusNemsFin2NonVacuousFinalAdequacy` — **final = fiber inequality**
    (aligned with `relocDemoBurden.sem`); `corpusNemsFin2_nv_*` — ∃ final, participation **substantive**, same **rcp**
    (`bothFibersHoldRouteProfile`).

  **SPEC_029 FE-4:** both rows package as **`LawfulAdequacyArchitecture`** (`corpusNemsFin2LawfulArchitecture`,
  `corpusNemsFin2NvLawfulArchitecture`) ⇒ **`universal_irreducible_adequacy_lawful`** / earned
  **`AbsoluteFrontierRawS1`** slices (`Portability/AbsoluteFrontierEarnedToy.lean`). **SPEC_030 MX7:**
  Level-1 **`corpusNemsFin2HFinal`** packages the same corridor row as **`HFinal CorpusStrataCarrier`**.

  **Faithful NEMS (`NemS.Framework`):** `NEMSFaithful.lean` — `Outer.ReflexiveLayer Framework`. **Level 3 bridge core**
  on the native index carrier: `NEMSFrameworkBridgeRecord.lean` (`nemsFrameworkNative_*`; two-point spine, not
  `Truth`/`diagonal`-aligned finality).

  **SPEC_035 Program 1 / S1a:** full lawful row stability under **`corpusStrataCarrierSwap`** —
  **`corpusNemsFin2NvLawfulArchitecture_pullbackAlong_corpusStrataCarrierSwap`** (via **`LawfulAdequacyArchitecture.mk.injEq`**), for
  **`isPullbackDisplay_comp_iff_of_pulledBackInner`** with **IC** + corpus **swap** outer.
-/

import AdequacyArchitecture.Instances.CorpusDischarge
import AdequacyArchitecture.Instances.CorpusLawfulRepresentation
import AdequacyArchitecture.Lawful.ComparePullback
import AdequacyArchitecture.Burden.IrreducibleAdequacy
import AdequacyArchitecture.Lawful.FinalConditionalSummit
import AdequacyArchitecture.Lawful.LawfulStructures
import AdequacyArchitecture.Lawful.MasterTheorem
import AdequacyArchitecture.Lawful.RelocationAlignedFinality
import AdequacyArchitecture.Summit.UniversalIrreducibleAdequacy
import AdequacyArchitecture.Toy.Fin2Model

namespace AdequacyArchitecture.Instances

open AdequacyArchitecture
open AdequacyArchitecture.Burden
open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open AdequacyArchitecture.Summit
open AdequacyArchitecture.Toy

/-- NEMS corpus-row burden (**B**) on `CorpusStrataCarrier` (= `Fin 2`). -/
abbrev corpusNemsFin2Burden : BurdenPredicates CorpusStrataCarrier :=
  relocDemoBurden

/-- NEMS corpus-row adequacy (**P**) — **Level 1** typed row: `repr` discriminator; no final accounts. -/
abbrev corpusNemsFin2Adequacy : AdequacyPredicates CorpusStrataCarrier :=
  toyPred

/-- **Level 2** adequacy: **only `final`** holds, with the **same fiber inequality** as `relocDemoBurden.sem`
(so final accounts are exactly `sem` relocation sources). -/
def corpusNemsFin2NonVacuousFinalAdequacy : AdequacyPredicates CorpusStrataCarrier where
  adeq := fun m A =>
    match m with
    | .final => A (⟨0, by decide⟩) ≠ A (⟨1, by decide⟩)
    | _ => False

/-- Route profile (**rcp**) used for corridor bridge rows (`RelocationAlignedFinality`). -/
abbrev corpusNemsFin2RouteProfile : RouteConstraintProfile CorpusStrataCarrier :=
  bothFibersHoldRouteProfile

theorem corpusNemsFin2_lawfulS2 : UniversalBurdenRelocationLawfulAtBurden corpusNemsFin2Burden :=
  universalBurdenRelocationLawfulAtBurden_relocDemoBurden

theorem corpusNemsFin2_nonempty_relocation_hygiene : NonemptyRelocationForBurden corpusNemsFin2Burden :=
  relocDemo_nonempty_relocation_for_burden

theorem corpusNemsFin2_final_participation : FinalAccountsParticipateInRelocation corpusNemsFin2Burden
    corpusNemsFin2Adequacy := by
  intro A hA
  exact False.elim (toyPred_no_final_adequacy A hA)

theorem corpusNemsFin2_route_inhonesty :
    LawfulRouteForcesRcpInhonesty corpusNemsFin2Burden corpusNemsFin2RouteProfile :=
  lawful_route_forces_inhonesty_relocDemo_bothFibersHold

theorem corpusNemsFin2_nonflat :
    NonFlatFinalityFromRouteConstraintFor corpusNemsFin2Adequacy corpusNemsFin2RouteProfile :=
  toy_nonFlatFinalityFor_toyPred corpusNemsFin2RouteProfile

/--
**SPEC_024 Level 1 — `HFinal` on `CorpusStrataCarrier`:** same completed stratified spine as the toy/corpus
representation, **`P` = `corpusNemsFin2Adequacy`** (**`toyPred`**), corridor **`rcp`**, corpus ridge witness,
non-flat from the Level-1 bridge row. Used by **`SPEC_030_MX7`** **`CertifiedFrontierRow`** packaging.
-/
def corpusNemsFin2HFinal : HFinal CorpusStrataCarrier :=
  mkHFinal corpusToyCompletedStratifiedLawfulAdequacyArchitecture corpusNemsFin2Adequacy
    corpusNemsFin2RouteProfile corpus_toy_ridge_cascade_witness corpusNemsFin2_nonflat

/-- Full **proof-essential core** + **non-flat** at the packaged `(B, P, rcp)` (corridor). -/
theorem corpusNemsFin2_bridge_core_and_nonflat :
    UniversalBurdenRelocationLawfulAtBurden corpusNemsFin2Burden ∧
      FinalAccountsParticipateInRelocation corpusNemsFin2Burden corpusNemsFin2Adequacy ∧
        LawfulRouteForcesRcpInhonesty corpusNemsFin2Burden corpusNemsFin2RouteProfile ∧
          NonFlatFinalityFromRouteConstraintFor corpusNemsFin2Adequacy corpusNemsFin2RouteProfile :=
  ⟨corpusNemsFin2_lawfulS2, corpusNemsFin2_final_participation,
    corpusNemsFin2_route_inhonesty, corpusNemsFin2_nonflat⟩

theorem corpusNemsFin2_relocation_aligned : RelocationAlignedWithFinality corpusNemsFin2Burden
    corpusNemsFin2Adequacy corpusNemsFin2RouteProfile :=
  ⟨corpusNemsFin2_nonempty_relocation_hygiene, corpusNemsFin2_final_participation,
    corpusNemsFin2_route_inhonesty⟩

theorem corpusNemsFin2_nonflat_from_minimal_lemma : NonFlatFinalityFromRouteConstraintFor
    corpusNemsFin2Adequacy corpusNemsFin2RouteProfile :=
  nonFlat_of_lawfulS2_final_participation_and_inhonesty corpusNemsFin2_lawfulS2
    corpusNemsFin2_final_participation corpusNemsFin2_route_inhonesty

/-! ### Level 2 — non-vacuous finality (same `B`, same `rcp`) -/

theorem corpusNemsFin2_nv_exists_final :
    ∃ A : Account CorpusStrataCarrier, corpusNemsFin2NonVacuousFinalAdequacy.adeq AdeqMode.final A := by
  use distinguishingAccount
  simp [corpusNemsFin2NonVacuousFinalAdequacy, distinguishingAccount]

theorem corpusNemsFin2_nv_final_participation :
    FinalAccountsParticipateInRelocation corpusNemsFin2Burden corpusNemsFin2NonVacuousFinalAdequacy := by
  intro A hA
  exact ⟨constantCollapse, BurdenMode.sem, BurdenMode.sel, relocationPair_relocDemo_sem_sel_of_sem hA⟩

theorem corpusNemsFin2_nv_route_inhonesty :
    LawfulRouteForcesRcpInhonesty corpusNemsFin2Burden corpusNemsFin2RouteProfile :=
  lawful_route_forces_inhonesty_relocDemo_bothFibersHold

theorem corpusNemsFin2_nv_nonflat : NonFlatFinalityFromRouteConstraintFor
    corpusNemsFin2NonVacuousFinalAdequacy corpusNemsFin2RouteProfile :=
  nonFlat_of_lawfulS2_final_participation_and_inhonesty corpusNemsFin2_lawfulS2
    corpusNemsFin2_nv_final_participation corpusNemsFin2_nv_route_inhonesty

/-- **Level-2** bundle: core + non-flat with **nonempty** final slice. -/
theorem corpusNemsFin2_nv_bridge_core_and_nonflat :
    (∃ A : Account CorpusStrataCarrier, corpusNemsFin2NonVacuousFinalAdequacy.adeq AdeqMode.final A) ∧
      UniversalBurdenRelocationLawfulAtBurden corpusNemsFin2Burden ∧
        FinalAccountsParticipateInRelocation corpusNemsFin2Burden corpusNemsFin2NonVacuousFinalAdequacy ∧
          LawfulRouteForcesRcpInhonesty corpusNemsFin2Burden corpusNemsFin2RouteProfile ∧
            NonFlatFinalityFromRouteConstraintFor corpusNemsFin2NonVacuousFinalAdequacy
              corpusNemsFin2RouteProfile :=
  ⟨corpusNemsFin2_nv_exists_final, corpusNemsFin2_lawfulS2, corpusNemsFin2_nv_final_participation,
    corpusNemsFin2_nv_route_inhonesty, corpusNemsFin2_nv_nonflat⟩

theorem corpusNemsFin2_nv_relocation_aligned : RelocationAlignedWithFinality corpusNemsFin2Burden
    corpusNemsFin2NonVacuousFinalAdequacy corpusNemsFin2RouteProfile :=
  ⟨corpusNemsFin2_nonempty_relocation_hygiene, corpusNemsFin2_nv_final_participation,
    corpusNemsFin2_nv_route_inhonesty⟩

/-- The non-flat conclusion is **substantive:** some final account fails `rcp` on some transform (`id`). -/
theorem corpusNemsFin2_nv_nonflat_witness :
    ∃ (A : Account CorpusStrataCarrier), corpusNemsFin2NonVacuousFinalAdequacy.adeq AdeqMode.final A ∧
      ∃ f : Transform CorpusStrataCarrier, ¬ corpusNemsFin2RouteProfile.holds f A := by
  use distinguishingAccount
  refine And.intro ?_ ?_
  · simp [corpusNemsFin2NonVacuousFinalAdequacy, distinguishingAccount]
  · use id
    simp [corpusNemsFin2RouteProfile, bothFibersHoldRouteProfile, distinguishingAccount]

/-! ### SPEC_029 FE-4 — lawful **`P,B`** rows ⇒ summit **S1** theorem (same shape as `AbsoluteFrontierRawS1`)

Packaging bridge-core **Level 1** (`corpusNemsFin2Adequacy`, **`relocDemoBurden`**) and **Level 2**
(`corpusNemsFin2NonVacuousFinalAdequacy`, same `B`) as **`LawfulAdequacyArchitecture`** instances so
**`universal_irreducible_adequacy_lawful`** applies. **Not** global raw `∀P,B`.
-/

theorem corpusNemsFin2_forces_each (m : AdeqMode) :
    AdequacyForcesSomeBurden corpusNemsFin2Adequacy corpusNemsFin2Burden m :=
  match m with
  | .repr => fun A hA =>
      ⟨BurdenMode.sem, by simpa [corpusNemsFin2Burden, corpusNemsFin2Adequacy, relocDemoBurden, toyPred] using hA⟩
  | .cert => fun A hA => False.elim hA
  | .obs => fun A hA => False.elim hA
  | .route => fun A hA => False.elim hA
  | .cont => fun A hA => False.elim hA
  | .final => fun A hA => False.elim hA

/-- Lawful class for **Level 1** NEMS `/` IC corridor row (**`B_IC`** = **`relocDemoBurden`**, not **`toyBurden`**). -/
def corpusNemsFin2LawfulArchitecture : LawfulAdequacyArchitecture CorpusStrataCarrier where
  P := corpusNemsFin2Adequacy
  B := corpusNemsFin2Burden
  forces_each := corpusNemsFin2_forces_each

theorem corpusNemsFin2_universal_irreducible_adequacy :
    UniversalIrreducibleAdequacyConjecture CorpusStrataCarrier corpusNemsFin2Adequacy corpusNemsFin2Burden :=
  universal_irreducible_adequacy_lawful corpusNemsFin2LawfulArchitecture

theorem corpusNemsFin2Nv_forces_each (m : AdeqMode) :
    AdequacyForcesSomeBurden corpusNemsFin2NonVacuousFinalAdequacy corpusNemsFin2Burden m :=
  match m with
  | .repr => fun A hA => False.elim hA
  | .cert => fun A hA => False.elim hA
  | .obs => fun A hA => False.elim hA
  | .route => fun A hA => False.elim hA
  | .cont => fun A hA => False.elim hA
  | .final => fun A hA =>
      ⟨BurdenMode.sem, by
        simpa [corpusNemsFin2Burden, relocDemoBurden, corpusNemsFin2NonVacuousFinalAdequacy] using hA⟩

/-- Lawful class for **Level 2** non-vacuous **final** adequacy row (same **`B`**). -/
def corpusNemsFin2NvLawfulArchitecture : LawfulAdequacyArchitecture CorpusStrataCarrier where
  P := corpusNemsFin2NonVacuousFinalAdequacy
  B := corpusNemsFin2Burden
  forces_each := corpusNemsFin2Nv_forces_each

theorem corpusNemsFin2Nv_universal_irreducible_adequacy :
    UniversalIrreducibleAdequacyConjecture CorpusStrataCarrier corpusNemsFin2NonVacuousFinalAdequacy
      corpusNemsFin2Burden :=
  universal_irreducible_adequacy_lawful corpusNemsFin2NvLawfulArchitecture

/-! ### SPEC_035 — compare-lift along **`corpusStrataCarrierSwap`** (nontrivial **S1a** display on corpus corridor) -/

theorem compareLiftAccountAlong_corpusStrataCarrierSwap (A : Account CorpusStrataCarrier) (i : CorpusStrataCarrier) :
    compareLiftAccountAlong corpusStrataCarrierSwap A i = A (corpusStrataCarrierSwap i) := by
  dsimp [compareLiftAccountAlong]
  apply propext
  constructor
  · rintro ⟨b, hbπ, hAb⟩
    have hb_eq := corpusStrataCarrierSwap_symm hbπ
    subst hb_eq
    exact hAb
  · intro hAi
    refine ⟨corpusStrataCarrierSwap i, ?_, hAi⟩
    simpa [Function.comp_apply] using congrFun corpusStrataCarrierSwap_involutive i

theorem corpusNemsFin2NonVacuousFinalAdequacy_pullbackAlong_corpusStrataCarrierSwap :
    corpusNemsFin2NonVacuousFinalAdequacy.pullbackAlongCompare corpusStrataCarrierSwap =
      corpusNemsFin2NonVacuousFinalAdequacy := by
  dsimp [AdequacyPredicates.pullbackAlongCompare]
  unfold corpusNemsFin2NonVacuousFinalAdequacy
  dsimp
  congr 1
  funext m A
  match m with
  | .repr => rfl
  | .cert => rfl
  | .obs => rfl
  | .route => rfl
  | .cont => rfl
  | .final =>
      simp only [compareLiftAccountAlong_corpusStrataCarrierSwap]
      dsimp only [corpusStrataCarrierSwap]
      exact congrArg Not (propext (Iff.intro Eq.symm Eq.symm))

theorem corpusNemsFin2Burden_pullbackAlong_corpusStrataCarrierSwap :
    corpusNemsFin2Burden.pullbackAlongCompare corpusStrataCarrierSwap = corpusNemsFin2Burden := by
  dsimp [BurdenPredicates.pullbackAlongCompare, corpusNemsFin2Burden, relocDemoBurden]
  congr 1
  funext m A
  match m with
  | .sem =>
      simp only [compareLiftAccountAlong_corpusStrataCarrierSwap]
      dsimp only [corpusStrataCarrierSwap]
      exact congrArg Not (propext (Iff.intro Eq.symm Eq.symm))
  | .sel => rfl
  | .res => rfl
  | .glue => rfl
  | .cont => rfl
  | .route => rfl

/--
**SPEC_035 Program 1 / S1a:** the **Level-2 NV** corpus **`LawfulAdequacyArchitecture`** is **fixed** by 𝒞-pullback along
**`corpusStrataCarrierSwap`** (not just **`P,B`** — the **`forces_each`** linkage agrees via **`compareLift`** involution).
-/
theorem corpusNemsFin2NvLawfulArchitecture_pullbackAlong_corpusStrataCarrierSwap :
    lawfulAdequacyArchitecture_pullbackAlongCompare corpusStrataCarrierSwap corpusNemsFin2NvLawfulArchitecture =
      corpusNemsFin2NvLawfulArchitecture := by
  dsimp only [lawfulAdequacyArchitecture_pullbackAlongCompare, corpusNemsFin2NvLawfulArchitecture]
  rw [LawfulAdequacyArchitecture.mk.injEq]
  refine And.intro ?_ ?_
  · exact corpusNemsFin2NonVacuousFinalAdequacy_pullbackAlong_corpusStrataCarrierSwap
  · exact corpusNemsFin2Burden_pullbackAlong_corpusStrataCarrierSwap

end AdequacyArchitecture.Instances
