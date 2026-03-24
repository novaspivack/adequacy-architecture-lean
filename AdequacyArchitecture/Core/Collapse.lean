/-
  Collapse / flattening operations on accounts.
-/

import AdequacyArchitecture.Core.Account
import AdequacyArchitecture.Core.Burden

universe u

namespace AdequacyArchitecture

variable {α : Type u}

abbrev CollapseOp (α : Type u) := Account α → Account α

def RemovesAllBurden (B : BurdenPredicates α) (C : CollapseOp α) (A : Account α) : Prop :=
  ∀ m : BurdenMode, ¬ B.burden m (C A)

end AdequacyArchitecture
