/-
  Ridge theorem **targets** (SPEC_010): outer-to-inner bridge, outer-to-middle bridge,
  Summit S2 recast, master cascade — `def : Prop` goals, not yet proved theorems.

  Once the completed class carries middle/inner laws, these become the next `theorem` spine.

  **Alignment with SPEC_011:** see `Lawful/RidgeSummitVsBridgeTargets.lean` (targets vs final
  `RidgeSummitStatements` shapes); B2 iff lemmas below eliminate impossible tag disjuncts.
-/

import AdequacyArchitecture.Core.Basic
import AdequacyArchitecture.Core.Transform
import AdequacyArchitecture.Core.Collapse
import AdequacyArchitecture.Lawful.CanonicalCarrier
import AdequacyArchitecture.Lawful.CompletedStratified
import AdequacyArchitecture.Lawful.LawfulStructures
import AdequacyArchitecture.Lawful.RelocationSummit

universe u

namespace AdequacyArchitecture.Lawful

open AdequacyArchitecture

/-- **Bridge 1 (ridge):** collapse either kills repr-adequacy or the **canonical burden carrier**
(at the realized burden witness) is tagged `residual`.

The second disjunct is **not** an unconstrained `∃ c : LawfulCarrier` (which would be vacuous:
pick `tag := residual`, `witness := True`). It is tied to `canonicalLawfulCarrierOfBurden`, whose
tag is `burdenCarrierTag = semanticRemainder` (see `CanonicalCarrier.lean`), so this branch is
**incompatible** with `CarrierTag.residual` under the current canonical definition—i.e. the
disjunction is driven by the first branch until a richer residual induction refines the carrier
story. What-Maps-Forget / Strata is meant to supply proofs under 𝒞. -/
def OuterToInnerBurdenBridgeTarget (α : Type u) : Prop :=
  ∀ (𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α)
    (C : CollapseOp α) (m : BurdenMode) (A : Account α),
    𝔠.strat.outer.B.burden m A →
    (¬ 𝔠.strat.outer.P.adeq AdeqMode.repr (C A)) ∨
    (∃ (h : 𝔠.strat.outer.B.burden m A),
      (canonicalLawfulCarrierOfBurden 𝔠.strat.outer.B m A h).carrier.tag = CarrierTag.residual)

/-- **Bridge 2 (ridge):** under burden, adequacy-preserving `f`, drop of burden at `m` on `f`,
and reappearance of burden on `f A`, some **canonical burden carrier at that reappearance**
`(m₂, f A)` is tagged `gluingObstruction` (APS / middle layer). Same non-vacuity pattern as
bridge 1: not an arbitrary `LawfulCarrier` with that tag. Under `burdenCarrierTag = semanticRemainder`,
this existential is still incompatible with `gluingObstruction` until a mode-dependent or
middle-layer carrier family refines tags. -/
def OuterToMiddleBurdenBridgeTarget (α : Type u) : Prop :=
  ∀ (𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α)
    (f : Transform α) (m : BurdenMode) (A : Account α),
    𝔠.strat.outer.B.burden m A →
    AdeqPreserving 𝔠.strat.outer.P AdeqMode.repr f →
    DropsBurdenMode 𝔠.strat.outer.B m f →
    (∃ (m₂ : BurdenMode), 𝔠.strat.outer.B.burden m₂ (f A)) →
    (∃ (m₂ : BurdenMode) (h' : 𝔠.strat.outer.B.burden m₂ (f A)),
      (canonicalLawfulCarrierOfBurden 𝔠.strat.outer.B m₂ (f A) h').carrier.tag = CarrierTag.gluingObstruction)

/-- Summit S2 **recast** (SPEC_010 §6): placeholder is the lawful relocation schema until
carrier-pattern constraints subsume it. -/
abbrev SummitRouteCarrierConstraintTarget (α : Type u) : Prop :=
  @UniversalBurdenRelocationLawful α

/-- Open ridge + route goals (bottleneck 1 is proved separately). Narrower than
`MasterCascadeThroughPhaseD` in `Lawful/ClassPhases.lean` (no Phase C/D conjuncts).

The **final** compressed summit family is `MasterStratifiedAdequacyCascade` in
`Lawful/RidgeSummitStatements.lean` (SPEC_011) — uses final bridge shapes + route-constraint profile. -/
def MasterStratifiedAdequacyCascadeTarget (α : Type u) : Prop :=
  OuterToInnerBurdenBridgeTarget α ∧ OuterToMiddleBurdenBridgeTarget α ∧ SummitRouteCarrierConstraintTarget α

end AdequacyArchitecture.Lawful
