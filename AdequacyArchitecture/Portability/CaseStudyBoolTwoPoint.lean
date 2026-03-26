/-
  **SPEC_028_EK7** — flagship **external-style** case study: **Bool** two-point lawful model.

  **Not** the `Fin 2` toy module — same proof obligations, carrier `Bool` for **portability**
  (CS / logic audience). See `specs/NOTES/EXTERNAL_CASE_STUDY_BOOL_TWO_POINT.md`.

  **SPEC_029 FE-5 v2:** second **bounded** stress carrier (`Bool` **≠** shared corpus `Fin 2` packaging) —
  see `specs/NOTES/FE5_BOOL_TWO_POINT_SCALE_CASE_STUDY.md`; earned **`AbsoluteFrontierRawS1`** slice below.
-/

import AdequacyArchitecture.Portability.InstantiationCalculus
import AdequacyArchitecture.Lawful.FinalConditionalSummit

universe u

namespace AdequacyArchitecture.Portability

open AdequacyArchitecture.Burden
open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open AdequacyArchitecture.Summit

/-- Account separating the two Boolean corners. -/
def boolDistinguishingAccount : Account Bool := fun b =>
  match b with
  | true => True
  | false => False

/-- Repr-mode adequacy = inequality on the two corners; semantic burden = same formula. -/
def boolOuterPred : AdequacyPredicates Bool where
  adeq := fun m A =>
    match m with
    | .repr => A true ≠ A false
    | _ => False

def boolOuterBurden : BurdenPredicates Bool where
  burden := fun m A =>
    match m with
    | .sem => A true ≠ A false
    | _ => False

theorem boolCorners_separate :
    boolDistinguishingAccount true ≠ boolDistinguishingAccount false := by
  intro h
  have hf : boolDistinguishingAccount false := by
    rw [← h]
    exact trivial
  cases hf

theorem bool_adequacy_forces_burden_repr :
    AdequacyForcesSomeBurden boolOuterPred boolOuterBurden AdeqMode.repr := by
  intro A h
  use BurdenMode.sem
  simpa [boolOuterBurden, boolOuterPred] using h

theorem bool_forces_each_mode (m : AdeqMode) :
    AdequacyForcesSomeBurden boolOuterPred boolOuterBurden m := by
  cases m
  · exact bool_adequacy_forces_burden_repr
  · intro A h; cases h
  · intro A h; cases h
  · intro A h; cases h
  · intro A h; cases h
  · intro A h; cases h

def boolLawfulArchitecture : LawfulAdequacyArchitecture Bool where
  P := boolOuterPred
  B := boolOuterBurden
  forces_each := bool_forces_each_mode

def boolBurdenVariationSigma :
    Σ' (m : BurdenMode), Σ' (A : Account Bool), Σ' (A' : Account Bool),
      boolOuterBurden.burden m A ∧ ¬ boolOuterBurden.burden m A' :=
  ⟨BurdenMode.sem,
    ⟨boolDistinguishingAccount,
      ⟨fun _ => True,
        And.intro
          (boolCorners_separate)
          (by simp [boolOuterBurden])⟩⟩⟩

def boolStratifiedLawfulArchitecture : StratifiedLawfulAdequacyArchitecture Bool where
  outer := boolLawfulArchitecture
  burden_variation := boolBurdenVariationSigma

def boolStratifiedInstantiation : StratifiedSummitInstantiation Bool where
  strat := boolStratifiedLawfulArchitecture

def boolSummitContractBase : SummitContractBase Bool :=
  SummitContractBase.ofLawful boolLawfulArchitecture

theorem bool_holds_summit_contract_s1 :
    UniversalIrreducibleAdequacyConjecture Bool boolOuterPred boolOuterBurden :=
  summit_s1_of_base boolSummitContractBase

theorem bool_holds_summit_contract_s1_via_stratified :
    UniversalIrreducibleAdequacyConjecture Bool boolOuterPred boolOuterBurden :=
  summit_s1_of_stratified boolStratifiedInstantiation

/--
**FE-5 v2:** same proposition as **`bool_holds_summit_contract_s1`**, under the **`AbsoluteFrontierRawS1`**
    Layer-**B** name — **Bool** carrier, **not** corpus **`CorpusStrataCarrier`** / Strata discharge (**no** `fe4_*` checkpoint).
-/
theorem fe5_bool_two_point_earned_absoluteFrontierRawS1 : AbsoluteFrontierRawS1 boolOuterPred boolOuterBurden :=
  bool_holds_summit_contract_s1

end AdequacyArchitecture.Portability
