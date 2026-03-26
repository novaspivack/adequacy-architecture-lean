/-
  B2 — Ridge bridge **unfoldings** (SPEC_010 §4): proved logical equivalences for the bridge
  `def`s under the current canonical carrier tag (`burdenCarrierTag = semanticRemainder`).

  These are not the substantive ridge theorems under 𝒞 (still open); they eliminate the
  second disjuncts and record what the targets **mean** until mode-dependent carriers refine tags.
-/

import AdequacyArchitecture.Lawful.BridgeTargets
import AdequacyArchitecture.Lawful.RidgeSummitStatements

universe u

namespace AdequacyArchitecture.Lawful

open AdequacyArchitecture

theorem outerToInnerBurdenBridgeTarget_iff (α : Type u) :
    OuterToInnerBurdenBridgeTarget α ↔
    (∀ (𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α) (C : CollapseOp α) (m : BurdenMode) (A : Account α),
      𝔠.strat.outer.B.burden m A → ¬ 𝔠.strat.outer.P.adeq AdeqMode.repr (C A)) := by
  apply Iff.intro
  · intro houter 𝔠 C m A hbd
    have hdisj :
        (¬ 𝔠.strat.outer.P.adeq AdeqMode.repr (C A)) ∨
          (∃ (h : 𝔠.strat.outer.B.burden m A),
            (canonicalLawfulCarrierOfBurden 𝔠.strat.outer.B m A h).carrier.tag = CarrierTag.residual) :=
      houter 𝔠 C m A hbd
    cases hdisj with
    | inl hneg => exact hneg
    | inr h2 =>
      rcases h2 with ⟨h', heq⟩
      exact False.elim ((canonicalLawfulCarrierOfBurden_ne_residual_tag 𝔠.strat.outer.B m A h') heq)
  · intro h 𝔠 C m A hbd
    exact Or.inl (h 𝔠 C m A hbd)

theorem outerToMiddleBurdenBridgeTarget_iff (α : Type u) :
    OuterToMiddleBurdenBridgeTarget α ↔
    (∀ (𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α) (f : Transform α) (m : BurdenMode) (A : Account α),
      𝔠.strat.outer.B.burden m A →
      AdeqPreserving 𝔠.strat.outer.P AdeqMode.repr f →
      DropsBurdenMode 𝔠.strat.outer.B m f →
      (∃ (m₂ : BurdenMode), 𝔠.strat.outer.B.burden m₂ (f A)) →
      False) := by
  apply Iff.intro
  · intro houter 𝔠 f m A hbd hadp hdrop hre
    have hcon :
        ∃ (m₃ : BurdenMode) (h' : 𝔠.strat.outer.B.burden m₃ (f A)),
          (canonicalLawfulCarrierOfBurden 𝔠.strat.outer.B m₃ (f A) h').carrier.tag =
            CarrierTag.gluingObstruction :=
      houter 𝔠 f m A hbd hadp hdrop hre
    rcases hcon with ⟨m₃, h3', heq⟩
    exact False.elim ((canonicalLawfulCarrierOfBurden_ne_gluing_tag 𝔠.strat.outer.B m₃ (f A) h3') heq)
  · intro h 𝔠 f m A hbd hadp hdrop hre
    exact False.elim (h 𝔠 f m A hbd hadp hdrop hre)

theorem nonFlatFinalityFromRouteConstraint_iff_forall_for (α : Type u) :
    NonFlatFinalityFromRouteConstraint α ↔
      ∀ (P : AdequacyPredicates α) (rcp : RouteConstraintProfile α),
        NonFlatFinalityFromRouteConstraintFor P rcp :=
  Iff.rfl

end AdequacyArchitecture.Lawful
