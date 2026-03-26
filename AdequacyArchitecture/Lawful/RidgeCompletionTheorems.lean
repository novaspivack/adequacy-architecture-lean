/-
  SPEC_012 — Scoped completion lemmas: NonFlat when no final adequacy (`nonFlatFinalityFor_of_no_final_adequacy`).
  S2-at-burden and global iff live in `Lawful/RelocationSummit.lean`; S1 over 𝒞 in `Summit/SummitOverClass.lean`.
-/

import AdequacyArchitecture.Lawful.RidgeSummitStatements

universe u

namespace AdequacyArchitecture.Lawful

open AdequacyArchitecture

variable {α : Type u}

theorem nonFlatFinalityFor_of_no_final_adequacy (P : AdequacyPredicates α) (rcp : RouteConstraintProfile α)
    (hP : ∀ (A : Account α), ¬ P.adeq AdeqMode.final A) :
    NonFlatFinalityFromRouteConstraintFor P rcp := by
  intro h
  rcases h with ⟨A, hA⟩
  exact False.elim (hP A hA)

end AdequacyArchitecture.Lawful
