/-
  Summit S2 shape over **lawful** route data (SPEC_008): `LawfulRouteDatum`, not raw `RouteDatum`.
-/

import AdequacyArchitecture.Core.Basic
import AdequacyArchitecture.Core.Route
import AdequacyArchitecture.Burden.RelocationClass
import AdequacyArchitecture.Lawful.LawfulStructures

universe u

namespace AdequacyArchitecture.Lawful

open AdequacyArchitecture.Burden (RelocationPair)

variable {α : Type u}

/-- Summit S2 with **lawful** (anti-trivial) route witnesses. -/
def UniversalBurdenRelocationLawful : Prop :=
  ∀ (B : BurdenPredicates α) (f : Transform α) (m₁ m₂ : BurdenMode) (A : Account α),
    RelocationPair B m₁ m₂ f A → ∃ r : LawfulRouteDatum α, r.datum.feature A ∧ r.datum.feature (f A)

/-- S2 **at a fixed** outer burden predicate `B` (SPEC_012 scoped completion). -/
def UniversalBurdenRelocationLawfulAtBurden (B : BurdenPredicates α) : Prop :=
  ∀ (f : Transform α) (m₁ m₂ : BurdenMode) (A : Account α),
    RelocationPair B m₁ m₂ f A → ∃ r : LawfulRouteDatum α, r.datum.feature A ∧ r.datum.feature (f A)

theorem universalBurdenRelocationLawful_iff_forall_burden :
    (∀ B : BurdenPredicates α, UniversalBurdenRelocationLawfulAtBurden B) ↔
    @UniversalBurdenRelocationLawful α :=
  Iff.rfl

/-- Same as `universalBurdenRelocationLawful_iff_forall_burden` with the global statement on the left (SPEC_012 wording). -/
theorem universalBurdenRelocationLawful_iff_forall_atBurden :
    @UniversalBurdenRelocationLawful α ↔ ∀ B : BurdenPredicates α, UniversalBurdenRelocationLawfulAtBurden B :=
  Iff.symm universalBurdenRelocationLawful_iff_forall_burden

theorem universalBurdenRelocationLawfulAtBurden_of_no_relocation (B : BurdenPredicates α)
    (h : ∀ (f : Transform α) (m₁ m₂ : BurdenMode) (A : Account α), ¬ RelocationPair B m₁ m₂ f A) :
    UniversalBurdenRelocationLawfulAtBurden B := by
  intro f m₁ m₂ A hp
  exact False.elim (h f m₁ m₂ A hp)

end AdequacyArchitecture.Lawful
