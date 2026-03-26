/-
  E1 — Continuation / viability: comparison is injective on continuations (no spurious identification).
-/

import AdequacyArchitecture.Residual.Strata

universe u

namespace AdequacyArchitecture.Dynamics

open ReflexiveArchitecture.Universal

/-- Viable continuation: the comparison map is **minimally exhaustive** (injective). -/
def ContinuationAdequate {α β : Type u} (π : α → β) : Prop :=
  MinimalExhaustive (Residual.rcsOfMap π)

end AdequacyArchitecture.Dynamics
