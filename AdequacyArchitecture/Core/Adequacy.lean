/-
  Typed adequacy predicates (per `AdeqMode`).
-/

import AdequacyArchitecture.Core.Modes
import AdequacyArchitecture.Core.Account

universe u

namespace AdequacyArchitecture

variable {α : Type u}

/-- Family of adequacy predicates indexed by mode. -/
structure AdequacyPredicates (α : Type u) where
  adeq : AdeqMode → Account α → Prop

/-- Bundled “typed adequacy” used in statements: pick a mode and ask `adeq m A`. -/
def Adeq (P : AdequacyPredicates α) (m : AdeqMode) (A : Account α) : Prop :=
  P.adeq m A

end AdequacyArchitecture
