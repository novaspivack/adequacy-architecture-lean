/-
  Anti-triviality lemmas for lawful routes (SPEC_008 Phase C).
-/

import AdequacyArchitecture.Lawful.LawfulStructures

universe u

namespace AdequacyArchitecture.Lawful

variable {α : Type u}

/-- A lawful route datum cannot satisfy `feature` for **every** account. -/
theorem not_forall_feature_of_lawfulRoute (r : LawfulRouteDatum α) :
    ¬∀ A : Account α, r.datum.feature A := by
  intro hall
  rcases r.nontrivial with ⟨A0, hn⟩
  exact hn (hall A0)

/-- The all-`True` route datum is **not** underlying any `LawfulRouteDatum`. -/
theorem no_lawful_all_true_routeDatum :
    ¬∃ r : LawfulRouteDatum α, ∀ A : Account α, r.datum.feature A := by
  rintro ⟨r, hall⟩
  exact not_forall_feature_of_lawfulRoute r hall

end AdequacyArchitecture.Lawful
