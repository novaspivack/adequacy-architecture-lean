/-
  SPEC_011 — Final intended ridge bridge theorems, coherence, route-constraint summit, master cascade.

  These `def : Prop` are the **theorem shapes** to prove (not the older tag-only `BridgeTargets`).
  Canonicality: inner residual is indexed by the **same** burden witness `h` as
  `canonicalLawfulCarrierOfBurden` (see `InnerResidualInducedByCanonical`).

  Old targets remain in `BridgeTargets.lean`; logical unfoldings in `BridgeTheorems.lean`.
-/

import AdequacyArchitecture.Core.Basic
import AdequacyArchitecture.Core.Transform
import AdequacyArchitecture.Burden.RelocationClass
import AdequacyArchitecture.Lawful.CompletedStratified
import AdequacyArchitecture.Lawful.MiddleInnerHooks

universe u

namespace AdequacyArchitecture.Lawful

open AdequacyArchitecture
open AdequacyArchitecture.Burden (RelocationPair)

variable {α : Type u}

/-- Inner residual on the **collapsed** account, tied to the realized burden witness `h` used for
`canonicalLawfulCarrierOfBurden` (Package A — canonicality discipline). -/
def InnerResidualInducedByCanonical (𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α)
    (C : CollapseOp α) (m : BurdenMode) (A : Account α)
    (_h : 𝔠.strat.outer.B.burden m A) : Prop :=
  𝔠.inner.domainResidual (C A)

/-- **Outer → inner** at a fixed completed stratified instance (SPEC_011 toy / restricted proofs). -/
def OuterToInnerBurdenBridgeAt (𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α) : Prop :=
  ∀ (C : CollapseOp α) (m : BurdenMode) (A : Account α),
    𝔠.strat.outer.B.burden m A →
    (¬ 𝔠.strat.outer.P.adeq AdeqMode.repr (C A)) ∨
    (∃ (h : 𝔠.strat.outer.B.burden m A), InnerResidualInducedByCanonical 𝔠 C m A h)

/-- **Outer → inner (final intended):** collapse kills repr-adequacy or inner residual is induced
on `C A`, witnessed along the canonical burden carrier’s proof `h`. -/
def OuterToInnerBurdenBridge (α : Type u) : Prop :=
  ∀ 𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α, OuterToInnerBurdenBridgeAt 𝔠

/-- Middle witness at the reappearance site: obstruction **or** gluing-compatible for the same
transform and **pre-image** account `A` (Package B — coverage). -/
def MiddleLayerWitnessCoversBurden (𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α)
    (f : Transform α) (A : Account α) (m₂ : BurdenMode) (A' : Account α)
    (_h' : 𝔠.strat.outer.B.burden m₂ A') : Prop :=
  𝔠.middle.gluingObstructionAt m₂ A' ∨ 𝔠.middle.gluingCompatible f A

def OuterToMiddleBurdenBridgeAt (𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α) : Prop :=
  ∀ (f : Transform α) (m : BurdenMode) (A : Account α),
    𝔠.strat.outer.B.burden m A →
    AdeqPreserving 𝔠.strat.outer.P AdeqMode.repr f →
    DropsBurdenMode 𝔠.strat.outer.B m f →
    (∃ (m₂ : BurdenMode), 𝔠.strat.outer.B.burden m₂ (f A)) →
    (∃ (m₂ : BurdenMode) (h' : 𝔠.strat.outer.B.burden m₂ (f A)),
      MiddleLayerWitnessCoversBurden 𝔠 f A m₂ (f A) h')

/-- **Outer → middle (final intended):** under relocation antecedents, ∃ middle witness covering
the reappeared burden at `(m₂, f A)`. -/
def OuterToMiddleBurdenBridge (α : Type u) : Prop :=
  ∀ 𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α, OuterToMiddleBurdenBridgeAt 𝔠

def MiddleInnerBridgeCoherenceAt (𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α) : Prop :=
  ∀ (m : BurdenMode) (A : Account α),
    (𝔠.inner.domainResidual A ∧ 𝔠.middle.gluingObstructionAt m A) → 𝔠.strat.outer.B.burden m A

/-- **Coherence:** simultaneous inner residual and middle obstruction at `(m, A)` implies outer
burden — prevents fragmented ridge consequences (Package C). -/
def MiddleInnerBridgeCoherence (α : Type u) : Prop :=
  ∀ 𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α, MiddleInnerBridgeCoherenceAt 𝔠

/-- Nontrivial **route-constraint profile** (Deliverable 5): not a bare existential `RouteDatum`;
use as the summit route layer conclusion. -/
structure RouteConstraintProfile (α : Type u) where
  holds : Transform α → Account α → Prop
  nontrivial : ∃ A : Account α, ∃ f : Transform α, ¬ holds f A

def CarrierPatternInducesRouteConstraintAt (𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α) : Prop :=
  ∀ (f : Transform α) (m₁ m₂ : BurdenMode) (A : Account α),
    RelocationPair 𝔠.strat.outer.B m₁ m₂ f A →
    ∃ rcp : RouteConstraintProfile α, rcp.holds f A

/-- Relocation induces a route-constraint profile that **holds** on `(f, A)` (constraint class, not
merely “some lawful route datum exists”). -/
def CarrierPatternInducesRouteConstraint (α : Type u) : Prop :=
  ∀ 𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α, CarrierPatternInducesRouteConstraintAt 𝔠

/-- Finality step at fixed `P` and `rcp`: if any final-adequate account exists, some final-adequate
account fails the profile along some transform (wire to `Finality/` later). -/
def NonFlatFinalityFromRouteConstraintFor (P : AdequacyPredicates α) (rcp : RouteConstraintProfile α) : Prop :=
  (∃ (A : Account α), P.adeq AdeqMode.final A) →
  (∃ (A : Account α), P.adeq AdeqMode.final A ∧ ∃ (f : Transform α), ¬ rcp.holds f A)

/-- Finality step: **all** `(P, rcp)` pairs satisfy `NonFlatFinalityFromRouteConstraintFor`. -/
def NonFlatFinalityFromRouteConstraint (α : Type u) : Prop :=
  ∀ (P : AdequacyPredicates α) (rcp : RouteConstraintProfile α),
    NonFlatFinalityFromRouteConstraintFor P rcp

/-- **Master Stratified Adequacy Cascade** (SPEC_011 §5) — compressed theorem family; subsumes the
narrower `MasterStratifiedAdequacyCascadeTarget` from `BridgeTargets.lean` once bridges + S2 recast
are proved in this shape. -/
def MasterStratifiedAdequacyCascade (α : Type u) : Prop :=
  OuterToInnerBurdenBridge α ∧
  OuterToMiddleBurdenBridge α ∧
  MiddleInnerBridgeCoherence α ∧
  CarrierPatternInducesRouteConstraint α ∧
  NonFlatFinalityFromRouteConstraint α

/-- Ridge segment of the master cascade at a fixed `𝔠` (excludes global `NonFlatFinalityFromRouteConstraint`). -/
def MasterStratifiedAdequacyCascadeRidgeAt (𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α) : Prop :=
  OuterToInnerBurdenBridgeAt 𝔠 ∧
  OuterToMiddleBurdenBridgeAt 𝔠 ∧
  MiddleInnerBridgeCoherenceAt 𝔠 ∧
  CarrierPatternInducesRouteConstraintAt 𝔠

/-- Full SPEC_011 cascade at fixed `𝔠` plus pointwise finality for chosen `P` and `rcp`. -/
def MasterStratifiedAdequacyCascadeAt (𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α)
    (P : AdequacyPredicates α) (rcp : RouteConstraintProfile α) : Prop :=
  MasterStratifiedAdequacyCascadeRidgeAt 𝔠 ∧
  NonFlatFinalityFromRouteConstraintFor P rcp

end AdequacyArchitecture.Lawful
