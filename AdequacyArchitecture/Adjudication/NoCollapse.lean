/-
  E4 — Adjudication does not collapse distinct cases: injective comparison (minimal exhaustion).
-/

import AdequacyArchitecture.Residual.Strata

universe u

namespace AdequacyArchitecture.Adjudication

open ReflexiveArchitecture.Universal

def NoAdjudicativeCollapse {α β : Type u} (π : α → β) : Prop :=
  MinimalExhaustive (Residual.rcsOfMap π)

end AdequacyArchitecture.Adjudication
