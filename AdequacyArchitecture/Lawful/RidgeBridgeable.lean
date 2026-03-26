/-
  SPEC_012 / full program — **compression layer** between ridge theorem *conclusions* and reusable
  **structural law** hypotheses.

  * **`RidgeCascadeWitness 𝔠`** — the four SPEC_011 ridge `…At` conjuncts at `𝔠` (what you have
    proved or assumed as a **witness** to lying in the ridge corridor).
  * **`RidgeBridgeable 𝔠`** — **law package (A + schematic):** canonicality discipline plus the
    one-mode / no-relocation schematic from `RidgeToyLikeContext`. This is **not** defeq to the
    cascade: from it we **derive** at least `CarrierPatternInducesRouteConstraintAt` with real
    content (`carrierPatternInducesRouteConstraintAt_of_ridgeBridgeable`). The remaining three
    bridges need **middle/inner hook** laws or a direct `RidgeCascadeWitness` / per-`𝔠` proofs.

  Corpus discharge can target **`RidgeBridgeable`** (structural) and/or **`RidgeCascadeWitness`**
  (full ridge), depending on how much is proved vs assumed for that artifact.
-/

import AdequacyArchitecture.Lawful.RidgeSummitStatements
import AdequacyArchitecture.Lawful.RidgeLawPackages
import AdequacyArchitecture.Lawful.RidgeToyLikeContext

universe u

namespace AdequacyArchitecture.Lawful

open AdequacyArchitecture
open AdequacyArchitecture.Burden (RelocationPair)

variable {α : Type u}

/-- Witness that the four SPEC_011 ridge predicates hold at `𝔠` (conclusion bundle). -/
structure RidgeCascadeWitness (𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α) : Prop where
  outerToInner : OuterToInnerBurdenBridgeAt 𝔠
  outerToMiddle : OuterToMiddleBurdenBridgeAt 𝔠
  middleInnerCoherence : MiddleInnerBridgeCoherenceAt 𝔠
  carrierPatternRouteConstraint : CarrierPatternInducesRouteConstraintAt 𝔠

theorem masterStratifiedAdequacyCascadeRidgeAt_of_ridgeCascadeWitness
    {𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α} (h : RidgeCascadeWitness 𝔠) :
    MasterStratifiedAdequacyCascadeRidgeAt 𝔠 :=
  ⟨h.outerToInner, h.outerToMiddle, h.middleInnerCoherence, h.carrierPatternRouteConstraint⟩

theorem ridgeCascadeWitness_of_masterStratifiedAdequacyCascadeRidgeAt
    {𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α} (h : MasterStratifiedAdequacyCascadeRidgeAt 𝔠) :
    RidgeCascadeWitness 𝔠 := by
  rcases h with ⟨h₁, h₂, h₃, h₄⟩
  exact ⟨h₁, h₂, h₃, h₄⟩

theorem ridgeCascadeWitness_iff_masterStratifiedAdequacyCascadeRidgeAt
    (𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α) :
    RidgeCascadeWitness 𝔠 ↔ MasterStratifiedAdequacyCascadeRidgeAt 𝔠 :=
  Iff.intro masterStratifiedAdequacyCascadeRidgeAt_of_ridgeCascadeWitness
    ridgeCascadeWitness_of_masterStratifiedAdequacyCascadeRidgeAt

/-- **Structural** ridge law package: Package A (canonicality) + one-mode / no-relocation schematic. -/
structure RidgeBridgeable (𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α) : Prop where
  canonicality : CanonicalityLaw 𝔠
  ridge_one_mode_schematic : ToyLikeRidgeOneMode 𝔠

/-- **Packaging theorem (real content):** empty relocation antecedent ⇒ route-constraint conjunct. -/
theorem carrierPatternInducesRouteConstraintAt_of_ridgeBridgeable
    {𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α} (h : RidgeBridgeable 𝔠) :
    CarrierPatternInducesRouteConstraintAt 𝔠 := by
  intro f m₁ m₂ A hp
  exact False.elim (h.ridge_one_mode_schematic.no_relocation_pair m₁ m₂ f A hp)

/-- Optional alias for advisor language (“master cascade bridgeability”). -/
abbrev MasterCascadeBridgeable (𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α) : Prop :=
  RidgeBridgeable 𝔠

end AdequacyArchitecture.Lawful
