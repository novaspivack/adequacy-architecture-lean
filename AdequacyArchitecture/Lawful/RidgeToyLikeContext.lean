/-
  Schematic sufficient conditions for Fin 2–style SPEC_011 ridge proofs (single outer burden mode,
  empty relocation). Used to document *why* the toy instance works; other instances satisfy
  `ToyLikeRidgeOneMode` by separate theorems.
-/

import AdequacyArchitecture.Core.Basic
import AdequacyArchitecture.Core.Transform
import AdequacyArchitecture.Burden.RelocationClass
import AdequacyArchitecture.Lawful.CompletedStratified

universe u

namespace AdequacyArchitecture.Lawful

open AdequacyArchitecture
open AdequacyArchitecture.Burden (RelocationPair)

variable {α : Type u}

/-- Hypotheses matching the **Fin 2 toy** pattern: only one burden mode carries load, and
`RelocationPair` never holds. -/
structure ToyLikeRidgeOneMode (𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α) : Prop where
  sem_only_burden :
    ∀ (m : BurdenMode) (A : Account α), 𝔠.strat.outer.B.burden m A → m = BurdenMode.sem
  no_relocation_pair :
    ∀ (m₁ m₂ : BurdenMode) (f : Transform α) (A : Account α),
      ¬ RelocationPair 𝔠.strat.outer.B m₁ m₂ f A

end AdequacyArchitecture.Lawful
