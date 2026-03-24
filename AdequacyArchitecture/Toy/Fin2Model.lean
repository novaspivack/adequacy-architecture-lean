/-
  Finite **rich** target model (`Fin 2`): fully proved `AdequacyForcesSomeBurden` and consequence lemmas.
  This is the strongest “earned” Phase‑1 fragment without importing Strata.
-/

import AdequacyArchitecture.Core.Basic
import AdequacyArchitecture.Burden.IrreducibleAdequacy
import AdequacyArchitecture.Burden.NoFreeCollapse

universe u

namespace AdequacyArchitecture.Toy

open AdequacyArchitecture.Burden

/-- Distinguishing account: first fiber differs from second. -/
def distinguishingAccount : Account (Fin 2) := fun i =>
  match i with
  | ⟨0, _⟩ => True
  | ⟨1, _⟩ => False

theorem distinguishing_ne : distinguishingAccount (⟨0, by decide⟩) ≠ distinguishingAccount (⟨1, by decide⟩) := by
  simp [distinguishingAccount]

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

theorem toy_B1 (A : Account (Fin 2)) (h : toyPred.adeq AdeqMode.repr A) :
    ∃ m : BurdenMode, toyBurden.burden m A :=
  toy_adequacy_forces_burden A h

/-- Collapse to constant account removes semantic burden on `toyBurden`. -/
def constantCollapse : CollapseOp (Fin 2) := fun _ => fun _ => True

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

end AdequacyArchitecture.Toy
