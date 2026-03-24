/-
  Burden predicates and irreducibility (minimal abstract layer).
-/

import AdequacyArchitecture.Core.Modes
import AdequacyArchitecture.Core.Account

universe u

namespace AdequacyArchitecture

variable {α : Type u}

/-- Witness that some burden mode is realized for account `A` at target `α`. -/
structure BurdenWitness (α : Type u) where
  mode : BurdenMode
  carrierTag : CarrierTag

/-- Family stating, for each burden mode, whether it is present. -/
structure BurdenPredicates (α : Type u) where
  burden : BurdenMode → Account α → Prop

/-- Burden present (first layer; “irreducible” strengthenings live in `Burden/IrreducibleAdequacy.lean`). -/
def BurdenPresent (B : BurdenPredicates α) (m : BurdenMode) (A : Account α) : Prop :=
  B.burden m A

end AdequacyArchitecture
