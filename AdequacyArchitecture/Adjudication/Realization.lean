/-
  Realization slot: minimal exhaustion of the comparison (injective adjudicative map).
-/

import AdequacyArchitecture.Residual.Strata

universe u

namespace AdequacyArchitecture.Adjudication

open ReflexiveArchitecture.Universal

def RealizationSlot {α β : Type u} (π : α → β) : Prop :=
  MinimalExhaustive (Residual.rcsOfMap π)

end AdequacyArchitecture.Adjudication
