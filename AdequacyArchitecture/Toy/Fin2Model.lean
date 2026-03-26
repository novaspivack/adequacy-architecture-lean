/-
  Finite **rich** target model (`Fin 2`): fully proved `AdequacyForcesSomeBurden` and consequence lemmas.
  This is the strongest “earned” Phase‑1 fragment without importing Strata.
-/

import AdequacyArchitecture.Core.Basic
import AdequacyArchitecture.Burden.IrreducibleAdequacy
import AdequacyArchitecture.Burden.NoFreeCollapse
import AdequacyArchitecture.Burden.RelocationClass
import AdequacyArchitecture.Lawful.MasterTheorem
import AdequacyArchitecture.Lawful.LawfulStructures
import AdequacyArchitecture.Lawful.StratifiedLawfulArchitecture
import AdequacyArchitecture.Lawful.CompletedStratified
import AdequacyArchitecture.Lawful.BottleneckTheorems
import AdequacyArchitecture.Lawful.RidgeSummitStatements
import AdequacyArchitecture.Lawful.RidgeBridgeable
import AdequacyArchitecture.Lawful.RidgeLawPackages
import AdequacyArchitecture.Lawful.RidgeCompletionTheorems
import AdequacyArchitecture.Lawful.RidgeToyLikeContext
import AdequacyArchitecture.Summit.UniversalIrreducibleAdequacy

universe u

namespace AdequacyArchitecture.Toy

open AdequacyArchitecture.Burden
open AdequacyArchitecture.Lawful (RidgeBridgeable RidgeCascadeWitness canonicality_law_holds
  carrierPatternInducesRouteConstraintAt_of_ridgeBridgeable
  ridgeCascadeWitness_of_masterStratifiedAdequacyCascadeRidgeAt)
open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Summit

/-- Distinguishing account: first fiber differs from second. -/
def distinguishingAccount : Account (Fin 2) := fun i =>
  match i with
  | ⟨0, _⟩ => True
  | ⟨1, _⟩ => False

theorem distinguishing_ne : distinguishingAccount (⟨0, by decide⟩) ≠ distinguishingAccount (⟨1, by decide⟩) := by
  simp [distinguishingAccount]

/-- Distinguishing route feature (same inequality as toy adequacy/burden). -/
def toyDistinguishingRouteDatum : RouteDatum (Fin 2) :=
  ⟨fun A => A (⟨0, by decide⟩) ≠ A (⟨1, by decide⟩)⟩

/-- Lawful route datum: constant-`True` account is **not** distinguishing. -/
def toyLawfulRouteDatum : LawfulRouteDatum (Fin 2) where
  datum := toyDistinguishingRouteDatum
  nontrivial := by
    refine ⟨fun _ => True, ?_⟩
    simp [toyDistinguishingRouteDatum]

/-- Repr-mode adequacy = “distinguishes the two points”; semantic burden = same formula. -/
def toyPred : AdequacyPredicates (Fin 2) where
  adeq := fun m A =>
    match m with
    | .repr => A (⟨0, by decide⟩) ≠ A (⟨1, by decide⟩)
    | _ => False

def toyBurden : BurdenPredicates (Fin 2) where
  burden := fun m A =>
    match m with
    | .sem => A (⟨0, by decide⟩) ≠ A (⟨1, by decide⟩)
    | _ => False

theorem toy_adequacy_forces_burden : AdequacyForcesSomeBurden toyPred toyBurden AdeqMode.repr := by
  intro A h
  use BurdenMode.sem
  simpa [toyBurden, toyPred] using h

/-- B1 at **every** adequacy mode: non-`repr` modes never hold, so `AdequacyForcesSomeBurden` is vacuous. -/
theorem toy_forces_each_mode (m : AdeqMode) : AdequacyForcesSomeBurden toyPred toyBurden m := by
  cases m
  · exact toy_adequacy_forces_burden
  · intro A h; cases h
  · intro A h; cases h
  · intro A h; cases h
  · intro A h; cases h
  · intro A h; cases h

/-- SPEC_008 lawful architecture instance for the toy model. -/
def toyLawfulArchitecture : LawfulAdequacyArchitecture (Fin 2) where
  P := toyPred
  B := toyBurden
  forces_each := toy_forces_each_mode

/-- SPEC_009: Σ' witness — semantic burden on `distinguishingAccount`, not on the constant account. -/
def toyBurdenVariationSigma :
    Σ' (m : BurdenMode), Σ' (A : Account (Fin 2)), Σ' (A' : Account (Fin 2)),
      toyBurden.burden m A ∧ ¬ toyBurden.burden m A' :=
  ⟨BurdenMode.sem, ⟨distinguishingAccount, ⟨fun _ => True, And.intro (by simp [toyBurden, distinguishingAccount]) (by simp [toyBurden])⟩⟩⟩

/-- Stratified lawful instance (outer + `burden_variation`). -/
def toyStratifiedLawfulAdequacyArchitecture : StratifiedLawfulAdequacyArchitecture (Fin 2) where
  outer := toyLawfulArchitecture
  burden_variation := toyBurdenVariationSigma

/-- SPEC_009 bottleneck 1 on the toy. -/
theorem toy_bottleneck_one_nontrivial_lawful_carrier :
    ∃ (m : BurdenMode) (A A' : Account (Fin 2)) (_ : toyBurden.burden m A),
      Nonempty (LawfulCarrier (Fin 2)) ∧ ¬ toyBurden.burden m A' :=
  bottleneck_one_nontrivial_lawful_carrier toyStratifiedLawfulAdequacyArchitecture

/-- Sigma bundle for bottleneck 1 (SPEC_010). -/
def toy_bottleneck_one_bundle : BottleneckOneBundle toyStratifiedLawfulAdequacyArchitecture :=
  bottleneck_one_bundle toyStratifiedLawfulAdequacyArchitecture

/-- Middle layer: no gluing in the minimal toy; obstruction tracks burden at each site. -/
def toyMiddleLayer : LawfulMiddleLayer (Fin 2) where
  gluingCompatible := fun _ _ => False
  gluingObstructionAt := fun m A => toyBurden.burden m A

/-- Inner layer: semantic burden as domain residual; trivial compare ⇒ no codomain residual. -/
def toyInnerHook : LawfulInnerHook (Fin 2) Unit where
  domainResidual := fun A => toyBurden.burden BurdenMode.sem A
  codomainResidual := fun _ => False

/-- SPEC_010 completed stratified instance: trivial compare to `Unit` + B1 middle/inner hooks. -/
def toyCompletedStratifiedLawfulAdequacyArchitecture : CompletedStratifiedLawfulAdequacyArchitecture (Fin 2) where
  strat := toyStratifiedLawfulAdequacyArchitecture
  compareCodomain := Unit
  compare := fun _ => ()
  middle := toyMiddleLayer
  inner := toyInnerHook

/-- **Earned summit S1** for `Fin 2` toy predicates: universal irreducible adequacy as a theorem. -/
theorem toy_universal_irreducible_adequacy :
    UniversalIrreducibleAdequacyConjecture (Fin 2) toyPred toyBurden :=
  universal_irreducible_adequacy_lawful toyLawfulArchitecture

/-- `RelocationPair` for `toyBurden` is impossible: only `sem` carries burden, and the three conjuncts contradict. -/
theorem relocation_pair_toyBurden_false (f : Transform (Fin 2)) (m₁ m₂ : BurdenMode) (A : Account (Fin 2))
    (h : RelocationPair toyBurden m₁ m₂ f A) : False := by
  rcases h with ⟨h₁, h₂, h₃⟩
  cases m₁ <;> cases m₂ <;> simp [toyBurden] at h₁ h₂ h₃
  · exact h₃ h₂

/-- Schematic hypotheses for the Fin 2 `𝔠` (single semantic burden mode, no relocation). -/
theorem toy_toyLikeRidgeOneMode : ToyLikeRidgeOneMode toyCompletedStratifiedLawfulAdequacyArchitecture where
  sem_only_burden := by
    intro m A h
    cases m
    · rfl
    · cases h
    · cases h
    · cases h
    · cases h
    · cases h
  no_relocation_pair := fun m₁ m₂ f A h => relocation_pair_toyBurden_false f m₁ m₂ A h

/-- Structural **RidgeBridgeable** (law package A + schematic), not the full ridge witness. -/
theorem toy_ridgeBridgeable : RidgeBridgeable toyCompletedStratifiedLawfulAdequacyArchitecture where
  canonicality := canonicality_law_holds toyCompletedStratifiedLawfulAdequacyArchitecture
  ridge_one_mode_schematic := toy_toyLikeRidgeOneMode

/-- Phase C (toy): middle obstruction predicate **is** outer semantic burden (definitionally). -/
theorem toy_middle_gluingObstructionAt_iff_burden (m : BurdenMode) (A : Account (Fin 2)) :
    toyMiddleLayer.gluingObstructionAt m A ↔ toyBurden.burden m A :=
  Iff.rfl

/-- Phase D (toy): relocation antecedent is empty, so inner residual disjunct is vacuously derivable. -/
theorem toy_phaseD_inner_residual_of_relocation (f : Transform (Fin 2)) (m₁ m₂ : BurdenMode) (A : Account (Fin 2))
    (h : RelocationPair toyBurden m₁ m₂ f A) :
    toyInnerHook.domainResidual A ∨ toyInnerHook.domainResidual (f A) :=
  False.elim (relocation_pair_toyBurden_false f m₁ m₂ A h)

/-- Lawful summit S2 **conditional** on `toyBurden`: vacuous (antecedent is false). -/
theorem toy_relocation_pair_yields_lawful_route (f : Transform (Fin 2)) (m₁ m₂ : BurdenMode) (A : Account (Fin 2))
    (h : RelocationPair toyBurden m₁ m₂ f A) :
    ∃ r : LawfulRouteDatum (Fin 2), r.datum.feature A ∧ r.datum.feature (f A) :=
  False.elim (relocation_pair_toyBurden_false f m₁ m₂ A h)

theorem toy_B1 (A : Account (Fin 2)) (h : toyPred.adeq AdeqMode.repr A) :
    ∃ m : BurdenMode, toyBurden.burden m A :=
  toy_adequacy_forces_burden A h

/-- Collapse to constant account removes semantic burden on `toyBurden`. -/
def constantCollapse : CollapseOp (Fin 2) := fun _ => fun _ => True

/-! ### SPEC_018 / SPEC_021 — `BurdenAdmitsRelocation` demo (non-vacuous antecedent)

Semantic burden as in `toyBurden`, plus **`sel` always true** so that after `constantCollapse` a relocation
pair **`sem → sel`** exists. This is **not** `toyBurden`; it exhibits a **nonempty** `RelocationPair` witness.
-/

def relocDemoBurden : BurdenPredicates (Fin 2) where
  burden := fun m A =>
    match m with
    | .sem => A (⟨0, by decide⟩) ≠ A (⟨1, by decide⟩)
    | .sel => True
    | _ => False

theorem relocationPair_relocDemo_sem_sel :
    RelocationPair relocDemoBurden BurdenMode.sem BurdenMode.sel constantCollapse distinguishingAccount := by
  refine And.intro ?h1 (And.intro ?h2 ?h3)
  · simp [relocDemoBurden, distinguishingAccount]
  · simp [relocDemoBurden, constantCollapse]
  · simp [relocDemoBurden]

/-- Any **`sem`**-burdened account relocates **`sem → sel`** along `constantCollapse` (cf.
`relocationPair_relocDemo_sem_sel`; SPEC_024 non-vacuous finality row). -/
theorem relocationPair_relocDemo_sem_sel_of_sem {A : Account (Fin 2)}
    (hA : relocDemoBurden.burden BurdenMode.sem A) :
    RelocationPair relocDemoBurden BurdenMode.sem BurdenMode.sel constantCollapse A := by
  refine And.intro hA (And.intro ?_ ?_)
  · simp [relocDemoBurden, constantCollapse]
  · simp [relocDemoBurden]

/-- Account with **both** fibers true (`Fin 2` “cube top”). -/
def constantTrueAccount : Account (Fin 2) := fun _ => True

/-- Drop the second fiber to `False`, keep the first. -/
def clearSecondFiber : Transform (Fin 2) := fun A => fun i : Fin 2 =>
  match i with
  | ⟨0, _⟩ => A (⟨0, by decide⟩)
  | ⟨1, _⟩ => False

/-- Map every fiber to `False` (independent of `A`). -/
def mapToAllFalse : Transform (Fin 2) := fun _A => fun _i => False

/-! ### SPEC_023 — hybrid burden for fieldwise bridge stress tests

Extends `relocDemoBurden` with **`route` = both fibers true** so final-shaped accounts (the
`fin2CounterexampleP` witnesses) can sit on genuine relocation **sources**, enabling
`FinalAccountsParticipateInRelocation` without changing `fin2CounterexampleP`.
-/

def participationDemoBurden : BurdenPredicates (Fin 2) where
  burden := fun m A =>
    match m with
    | .sem => A (⟨0, by decide⟩) ≠ A (⟨1, by decide⟩)
    | .sel => True
    | .route => A (⟨0, by decide⟩) ∧ A (⟨1, by decide⟩)
    | _ => False

theorem relocationPair_participationDemo_route_sem :
    RelocationPair participationDemoBurden BurdenMode.route BurdenMode.sem clearSecondFiber
      constantTrueAccount := by
  refine And.intro ?h1 (And.intro ?h2 ?h3)
  · simp [participationDemoBurden, constantTrueAccount]
  · simp [participationDemoBurden, clearSecondFiber, constantTrueAccount]
  · simp [participationDemoBurden, clearSecondFiber, constantTrueAccount]

theorem relocationPair_participationDemo_route_sem_of {A : Account (Fin 2)}
    (hA : A (⟨0, by decide⟩) ∧ A (⟨1, by decide⟩)) :
    RelocationPair participationDemoBurden BurdenMode.route BurdenMode.sem clearSecondFiber A := by
  rcases hA with ⟨h0, h1⟩
  refine And.intro (And.intro h0 h1) (And.intro ?_ ?_)
  · intro ⟨_, hf⟩
    exact hf
  · simp [participationDemoBurden, clearSecondFiber]
    exact h0

theorem relocationPair_participationDemo_route_sel :
    RelocationPair participationDemoBurden BurdenMode.route BurdenMode.sel mapToAllFalse
      constantTrueAccount := by
  refine And.intro ?h1 (And.intro ?h2 ?h3)
  · simp [participationDemoBurden, constantTrueAccount]
  · simp [participationDemoBurden, mapToAllFalse]
  · simp [participationDemoBurden]

theorem constant_removes_all_burden (A : Account (Fin 2)) : RemovesAllBurden toyBurden constantCollapse A := by
  intro m
  cases m <;> simp [toyBurden, constantCollapse]

theorem toy_not_adequate_after_constant_collapse (A : Account (Fin 2))
    (hA : toyPred.adeq AdeqMode.repr A) :
    ¬ toyPred.adeq AdeqMode.repr (constantCollapse A) := by
  apply no_free_adequate_collapse toyPred toyBurden AdeqMode.repr constantCollapse A hA
  · intro A' h'
    use BurdenMode.sem
    simpa [toyBurden, toyPred] using h'
  · exact constant_removes_all_burden A

/-! ## SPEC_011 — ridge bridge theorems at the toy `𝔠` (`…At` predicates) -/

theorem toy_outerToInnerBurdenBridgeAt :
    OuterToInnerBurdenBridgeAt toyCompletedStratifiedLawfulAdequacyArchitecture := by
  intro C m A hbd
  match m with
  | .sem =>
    simp [InnerResidualInducedByCanonical, toyCompletedStratifiedLawfulAdequacyArchitecture, toyInnerHook]
    by_cases hadeq : toyPred.adeq AdeqMode.repr (C A)
    · exact Or.inr ⟨hbd, by simpa [InnerResidualInducedByCanonical, toyInnerHook, toyBurden, toyPred] using hadeq⟩
    · exact Or.inl hadeq
  | .sel =>
    cases hbd
  | .res =>
    cases hbd
  | .glue =>
    cases hbd
  | .cont =>
    cases hbd
  | .route =>
    cases hbd

/-- Antecedent of `OuterToMiddleBurdenBridge` is inconsistent on the toy (`DropsBurden` vs burden on `f A`). -/
theorem toy_outerToMiddleBurdenBridgeAt :
    OuterToMiddleBurdenBridgeAt toyCompletedStratifiedLawfulAdequacyArchitecture := by
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
  | .sel =>
    cases hbd
  | .res =>
    cases hbd
  | .glue =>
    cases hbd
  | .cont =>
    cases hbd
  | .route =>
    cases hbd

theorem toy_middleInnerBridgeCoherenceAt :
    MiddleInnerBridgeCoherenceAt toyCompletedStratifiedLawfulAdequacyArchitecture := by
  intro m A h
  rcases h with ⟨_hdom, hg⟩
  match m with
  | .sem =>
    have hgl : toyMiddleLayer.gluingObstructionAt BurdenMode.sem A := by
      simpa [toyCompletedStratifiedLawfulAdequacyArchitecture] using hg
    have hm := (toy_middle_gluingObstructionAt_iff_burden BurdenMode.sem A).mp hgl
    convert hm using 1
  | .sel =>
    cases (toy_middle_gluingObstructionAt_iff_burden BurdenMode.sel A).mp
      (by simpa [toyCompletedStratifiedLawfulAdequacyArchitecture] using hg)
  | .res =>
    cases (toy_middle_gluingObstructionAt_iff_burden BurdenMode.res A).mp
      (by simpa [toyCompletedStratifiedLawfulAdequacyArchitecture] using hg)
  | .glue =>
    cases (toy_middle_gluingObstructionAt_iff_burden BurdenMode.glue A).mp
      (by simpa [toyCompletedStratifiedLawfulAdequacyArchitecture] using hg)
  | .cont =>
    cases (toy_middle_gluingObstructionAt_iff_burden BurdenMode.cont A).mp
      (by simpa [toyCompletedStratifiedLawfulAdequacyArchitecture] using hg)
  | .route =>
    cases (toy_middle_gluingObstructionAt_iff_burden BurdenMode.route A).mp
      (by simpa [toyCompletedStratifiedLawfulAdequacyArchitecture] using hg)

theorem toy_carrierPatternInducesRouteConstraintAt :
    CarrierPatternInducesRouteConstraintAt toyCompletedStratifiedLawfulAdequacyArchitecture :=
  carrierPatternInducesRouteConstraintAt_of_ridgeBridgeable toy_ridgeBridgeable

theorem toy_masterStratifiedAdequacyCascadeRidgeAt :
    MasterStratifiedAdequacyCascadeRidgeAt toyCompletedStratifiedLawfulAdequacyArchitecture :=
  ⟨toy_outerToInnerBurdenBridgeAt, toy_outerToMiddleBurdenBridgeAt, toy_middleInnerBridgeCoherenceAt,
    toy_carrierPatternInducesRouteConstraintAt⟩

theorem toy_ridgeCascadeWitness : RidgeCascadeWitness toyCompletedStratifiedLawfulAdequacyArchitecture :=
  ridgeCascadeWitness_of_masterStratifiedAdequacyCascadeRidgeAt toy_masterStratifiedAdequacyCascadeRidgeAt

/-! ### `NonFlat` finality (toy `P` has no `final` adequacy) -/

theorem toyPred_no_final_adequacy (A : Account (Fin 2)) : ¬ toyPred.adeq AdeqMode.final A := by
  simp [toyPred]

theorem toy_nonFlatFinalityFor_toyPred (rcp : RouteConstraintProfile (Fin 2)) :
    NonFlatFinalityFromRouteConstraintFor toyPred rcp :=
  nonFlatFinalityFor_of_no_final_adequacy toyPred rcp toyPred_no_final_adequacy

theorem toy_masterStratifiedAdequacyCascadeAt (rcp : RouteConstraintProfile (Fin 2)) :
    MasterStratifiedAdequacyCascadeAt toyCompletedStratifiedLawfulAdequacyArchitecture toyPred rcp :=
  ⟨toy_masterStratifiedAdequacyCascadeRidgeAt, toy_nonFlatFinalityFor_toyPred rcp⟩

end AdequacyArchitecture.Toy
