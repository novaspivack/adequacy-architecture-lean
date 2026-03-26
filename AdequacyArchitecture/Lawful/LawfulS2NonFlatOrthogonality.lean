/-
  SPEC_022 — **Lawful S2 vs non-flat finality:** orthogonality / obstruction.

  There is **no** purely logical implication from `UniversalBurdenRelocationLawfulAtBurden B` to
  `NonFlatFinalityFromRouteConstraintFor P rcp` without **linking** assumptions tying the outer burden,
  adequacy `P`, and route profile `rcp` (e.g. through a completed stratified instance and ridge packaging).

  This module gives a **Fin 2** counterexample: vacuous lawful S2 (`toyBurden`) while `NonFlatFinality…`
  fails for an independent `(P, rcp)`.
-/

import AdequacyArchitecture.Lawful.FinalConditionalSummit
import AdequacyArchitecture.Lawful.SummitS2Frontier

namespace AdequacyArchitecture.Lawful.FinalConditionalSummit

open AdequacyArchitecture.Toy

/-- Final adequacy = **both** fibers true (nontrivial “final” witness on `Fin 2`). -/
def fin2CounterexampleP : AdequacyPredicates (Fin 2) where
  adeq := fun m A =>
    match m with
    | .final => A (⟨0, by decide⟩) ∧ A (⟨1, by decide⟩)
    | _ => False

/-- Route constraint: equality of fibers **or** first fiber; fails e.g. on `(False, True)` (nontrivial). -/
def fin2CounterexampleRcp : RouteConstraintProfile (Fin 2) where
  holds := fun _ A =>
    (A (⟨0, by decide⟩) = A (⟨1, by decide⟩)) ∨ A (⟨0, by decide⟩)
  nontrivial := by
    use fun i => match i with | ⟨0, _⟩ => False | ⟨1, _⟩ => True
    use id
    simp

private theorem fin2_exists_final_counterexample :
    ∃ A : Account (Fin 2), fin2CounterexampleP.adeq AdeqMode.final A := by
  use fun _ => True
  simp [fin2CounterexampleP]

private theorem fin2_final_implies_holds_all (A : Account (Fin 2)) (f : Transform (Fin 2))
    (hf : fin2CounterexampleP.adeq AdeqMode.final A) :
    fin2CounterexampleRcp.holds f A := by
  simp [fin2CounterexampleP] at hf
  simp [fin2CounterexampleRcp, hf]

/-- The non-flat implication is **false**: final accounts exist, but **every** final account passes
**every** transform’s constraint — so the second conjunct of `NonFlatFinalityFromRouteConstraintFor` never
fires. -/
theorem not_nonFlat_fin2_counterexample :
    ¬ NonFlatFinalityFromRouteConstraintFor fin2CounterexampleP fin2CounterexampleRcp := by
  intro h
  rcases fin2_exists_final_counterexample with ⟨A0, hA0⟩
  have h2 := h ⟨A0, hA0⟩
  rcases h2 with ⟨A, ⟨hA, ⟨f, hn⟩⟩⟩
  have := fin2_final_implies_holds_all A f hA
  exact hn this

/-- **Obstruction:** lawful S2 can hold **vacuously** while non-flat finality fails for unrelated `(P, rcp)`. -/
theorem exists_lawfulS2_nonflat_fail :
    ∃ (B : BurdenPredicates (Fin 2)) (P : AdequacyPredicates (Fin 2)) (rcp : RouteConstraintProfile (Fin 2)),
      UniversalBurdenRelocationLawfulAtBurden B ∧ ¬ NonFlatFinalityFromRouteConstraintFor P rcp :=
  ⟨toyBurden, fin2CounterexampleP, fin2CounterexampleRcp,
    And.intro universalBurdenRelocationLawfulAtBurden_toyBurden not_nonFlat_fin2_counterexample⟩

/-- There is **no** universal implication from lawful S2 **at `B` alone** to non-flat `P, rcp` — the
hypotheses are **orthogonal** without a bridge linking `B`, `P`, and `rcp`. -/
theorem not_forall_lawfulS2_implies_nonflat :
    ¬ (∀ (B : BurdenPredicates (Fin 2)) (P : AdequacyPredicates (Fin 2)) (rcp : RouteConstraintProfile (Fin 2)),
        UniversalBurdenRelocationLawfulAtBurden B → NonFlatFinalityFromRouteConstraintFor P rcp) := by
  intro h
  have := h toyBurden fin2CounterexampleP fin2CounterexampleRcp universalBurdenRelocationLawfulAtBurden_toyBurden
  exact not_nonFlat_fin2_counterexample this

/-- **Non-vacuous** lawful S2 (`relocDemoBurden`) does **not**, by itself, discharge the same
counterexample `NonFlatFinality…` — the `(P, rcp)` finality data are independent unless linked by a bridge. -/
theorem relocDemo_lawfulS2_does_not_imply_counterexample_nonflat :
    UniversalBurdenRelocationLawfulAtBurden relocDemoBurden →
    ¬ NonFlatFinalityFromRouteConstraintFor fin2CounterexampleP fin2CounterexampleRcp :=
  fun _ => not_nonFlat_fin2_counterexample

/-- **Structural moral (proposition):** `HFinal.nonFlat` cannot be **removed** in favor of lawful S2 alone;
  any summit link must name **additional** alignment between relocation lawfulness and the `(P, rcp)`
  finality profile. -/
def LawfulS2OrthogonalToNonFlatHypothesis : Prop :=
  ∃ (B : BurdenPredicates (Fin 2)) (P : AdequacyPredicates (Fin 2)) (rcp : RouteConstraintProfile (Fin 2)),
    UniversalBurdenRelocationLawfulAtBurden B ∧ ¬ NonFlatFinalityFromRouteConstraintFor P rcp

theorem lawfulS2_orthogonal_to_nonflat : LawfulS2OrthogonalToNonFlatHypothesis :=
  exists_lawfulS2_nonflat_fail

end AdequacyArchitecture.Lawful.FinalConditionalSummit
