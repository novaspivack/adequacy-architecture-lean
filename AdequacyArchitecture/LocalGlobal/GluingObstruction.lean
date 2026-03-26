/-
  D2 — Gluing / descent: local data → global composition (Strata middle layer).

  **Strata:** `composition_from_tracking_and_gluing` (`Middle/CompositionExactness.lean`); see SPEC_001.
-/

import AdequacyArchitecture.Core.Basic
import ReflexiveArchitecture.Middle.CompositionExactness

universe u

namespace AdequacyArchitecture.LocalGlobal

open ReflexiveArchitecture

/-- Finite tracking + gluing ⇒ indexed composition (Strata middle layer). -/
theorem composition_from_tracking_and_gluing {S : Type u} [M : Middle.RealizationLayer S]
    (h : M.HasFiniteTracking ∧ M.HasGluing) : M.ICompIdx :=
  Middle.composition_from_tracking_and_gluing h

/-- Optional slot for a burden-theoretic obstruction witness (Adequacy-native). -/
structure GluingObstruction (α : Type u) where
  witness : Prop

end AdequacyArchitecture.LocalGlobal
