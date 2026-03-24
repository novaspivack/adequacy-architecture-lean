/-
  Carriers for burden (abstract tagging; instances specialize).
-/

import AdequacyArchitecture.Core.Modes
import AdequacyArchitecture.Core.Account

universe u

namespace AdequacyArchitecture

variable {α : Type u}

/-- A carrier slot for burden: a tag plus a witness `Prop` (refine to types later). -/
structure Carrier (α : Type u) where
  tag : CarrierTag
  witness : Prop

def AdmissibleCarrier (_m : BurdenMode) (_A : Account α) (_c : Carrier α) : Prop :=
  True

end AdequacyArchitecture
