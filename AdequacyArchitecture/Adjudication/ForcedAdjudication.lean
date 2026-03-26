/-
  E3 — Forced adjudication: residual forces nontrivial distinction (non-exhaustive comparison).
-/

import AdequacyArchitecture.Residual.Strata

universe u

namespace AdequacyArchitecture.Adjudication

open ReflexiveArchitecture.Universal

def ForcedAdjudicationWitness {α β : Type u} (π : α → β) : Prop :=
  NonExhaustive (Residual.rcsOfMap π)

end AdequacyArchitecture.Adjudication
