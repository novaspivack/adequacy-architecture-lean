/-
  A2 — Burden carrier existence: for each adequacy mode, a burden mode + admissible carrier slot.
-/

import AdequacyArchitecture.Core.Basic
import AdequacyArchitecture.Foundation.AdequacyInterface

universe u

namespace AdequacyArchitecture.Foundation

variable {α : Type u}

/-- Pick a canonical burden mode for each adequacy mode (first approximation; refine to functorial assignment). -/
def burdenModeOfAdeq : AdeqMode → BurdenMode
  | .repr => .sem
  | .cert => .res
  | .obs => .sel
  | .route => .route
  | .cont => .cont
  | .final => .res

theorem carrier_exists_of_adequacy_mode (m : BurdenMode) (A : Account α) :
    ∃ c : Carrier α, AdmissibleCarrier m A c :=
  ⟨⟨CarrierTag.residual, True⟩, trivial⟩

theorem burden_mode_has_admissible_carrier (m : AdeqMode) (A : Account α) :
    ∃ c : Carrier α, AdmissibleCarrier (burdenModeOfAdeq m) A c :=
  carrier_exists_of_adequacy_mode _ _

end AdequacyArchitecture.Foundation
