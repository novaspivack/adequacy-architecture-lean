/-
  B2 — No free adequate collapse (strong template): if adequacy **always** implies some burden,
  collapse cannot remove all burden and remain adequate in the same mode.
-/

import AdequacyArchitecture.Core.Basic
import AdequacyArchitecture.Burden.IrreducibleAdequacy

universe u

namespace AdequacyArchitecture.Burden

variable {α : Type u}

/-- **Strong form:** if *every* adequate account in mode `m` has some burden, collapse cannot clear all burden and stay adequate. -/
theorem no_free_adequate_collapse
    (P : AdequacyPredicates α) (B : BurdenPredicates α) (m : AdeqMode) (C : CollapseOp α) (A : Account α)
    (_hA : P.adeq m A)
    (hstrong : ∀ A' : Account α, P.adeq m A' → ∃ m' : BurdenMode, B.burden m' A')
    (hrem : RemovesAllBurden B C A) :
    ¬ P.adeq m (C A) := by
  intro h'
  obtain ⟨m', hm'⟩ := hstrong (C A) h'
  exact absurd hm' (hrem m')

/-- Program-plan label “weak” — same theorem; strength is entirely in hypothesis `hstrong`. -/
abbrev no_free_adequate_collapse_weak := @no_free_adequate_collapse

theorem removes_all_burden_implies_inadequate
    (P : AdequacyPredicates α) (B : BurdenPredicates α) (m : AdeqMode) (C : CollapseOp α) (A : Account α)
    (_hA : P.adeq m A) (hstrong : ∀ A', P.adeq m A' → ∃ m', B.burden m' A') (hrem : RemovesAllBurden B C A) :
    ¬ P.adeq m (C A) :=
  no_free_adequate_collapse P B m C A _hA hstrong hrem

end AdequacyArchitecture.Burden
