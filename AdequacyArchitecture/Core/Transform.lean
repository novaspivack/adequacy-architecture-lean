/-
  Account transformations, adequacy preservation, carrier dropping, relocation (definitions).
-/

import AdequacyArchitecture.Core.Account
import AdequacyArchitecture.Core.Adequacy
import AdequacyArchitecture.Core.Burden

universe u

namespace AdequacyArchitecture

variable {α : Type u}

abbrev Transform (α : Type u) := Account α → Account α

def AdeqPreserving (P : AdequacyPredicates α) (m : AdeqMode) (f : Transform α) : Prop :=
  ∀ A : Account α, P.adeq m A → P.adeq m (f A)

def DropsBurdenMode (B : BurdenPredicates α) (m : BurdenMode) (f : Transform α) : Prop :=
  ∀ A : Account α, B.burden m A → ¬ B.burden m (f A)

/-- Relocation: burden `m` is dropped but some other mode picks it up (schematic binary relation on modes). -/
def RelocatesBurden
    (B : BurdenPredicates α) (m m' : BurdenMode) (f : Transform α) : Prop :=
  ∃ A : Account α, B.burden m A ∧ ¬ B.burden m (f A) ∧ B.burden m' (f A)

end AdequacyArchitecture
