/-
  **SPEC_025 — Phase B:** uniform **semantic tracking** (morphism template) without global `∀ F`.

  `NEMStrongSemanticGlue` already states the local iff bridges at one anchor. This module packages the
  **uniform promotion** to a bipartite witness bundle (`NemSemanticTrackedContent`) reusable from any
  anchored instance, and records **halting-coherence** (`Truth` vs `RT`) via the Instantiation linkage.
-/

import AdequacyArchitecture.Instances.NEMSSemanticGlue

namespace AdequacyArchitecture.Instances

open NemS.Framework
open NemS
open NemS.MFRR

/-! ### Tracked content (uniform extraction) -/

/-- **Bipartite existential payload** at one `Framework`: grid-level `Truth` **and** coded `RT`. -/
structure NemSemanticTrackedContent (F : Framework) [DiagonalCapable F] : Prop where
  truth : ExistentialTruthWitness F
  rt : ExistentialRTWitness F

variable {F : Framework} [DiagonalCapable F]
variable {P : AdequacyPredicates Framework} {A : Account Framework}

/-- Uniform promotion from **anchored glue** (any anchor, any `DiagonalCapable` witness). -/
theorem NemSemanticTrackedContent.ofAnchored (h : NEMAnchoredSemanticGlue F P A) :
    NemSemanticTrackedContent F :=
  ⟨existential_truth_of_anchored h, existential_rt_of_anchored h⟩

/-- From strong glue + `A F`, without bundling the anchored `structure`. -/
theorem NemSemanticTrackedContent.ofStrongGlue_anchor (g : NEMStrongSemanticGlue F P A) (hA : A F) :
    NemSemanticTrackedContent F :=
  NemSemanticTrackedContent.ofAnchored ⟨g, hA⟩

/-- **Uniform tracker** (Phase B naming): local `P.final` + iff bridges **at this** `F` only. -/
abbrev NEMUniformSemanticTracker (F : Framework) [DiagonalCapable F]
    (P : AdequacyPredicates Framework) (A : Account Framework) : Prop :=
  NEMStrongSemanticGlue F P A

theorem NemSemanticTrackedContent.of_uniform_tracker_anchor (tr : NEMUniformSemanticTracker F P A)
    (hA : A F) : NemSemanticTrackedContent F :=
  NemSemanticTrackedContent.ofStrongGlue_anchor tr hA

end AdequacyArchitecture.Instances
