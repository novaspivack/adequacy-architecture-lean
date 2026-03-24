/-
  B1 — Irreducible adequacy burden (abstract + linkage predicates).
-/

import AdequacyArchitecture.Core.Basic

universe u

namespace AdequacyArchitecture.Burden

variable {α : Type u}

/-- Adequacy in mode `m` forces some burden mode to be present. This is the **semantic core** of B1 (not smuggled into `RichTarget`). -/
def AdequacyForcesSomeBurden (P : AdequacyPredicates α) (B : BurdenPredicates α) (m : AdeqMode) : Prop :=
  ∀ A : Account α, P.adeq m A → ∃ m' : BurdenMode, B.burden m' A

theorem irreducible_burden_of_adequacy (P : AdequacyPredicates α) (B : BurdenPredicates α) (m : AdeqMode)
    (A : Account α) (hlink : AdequacyForcesSomeBurden P B m) (hA : P.adeq m A) :
    ∃ m' : BurdenMode, B.burden m' A :=
  hlink A hA

/-- With richness present, the same conclusion uses an explicit richness-indexed hypothesis (strongest honest abstract form). -/
theorem irreducible_burden_of_adequacy_rich [RichTarget α] (P : AdequacyPredicates α) (B : BurdenPredicates α)
    (m : AdeqMode) (A : Account α)
    (hlink : RichTarget α → AdequacyForcesSomeBurden P B m) (hA : P.adeq m A) :
    ∃ m' : BurdenMode, B.burden m' A :=
  hlink ‹RichTarget α› A hA

end AdequacyArchitecture.Burden
