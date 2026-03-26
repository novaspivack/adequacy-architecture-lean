/-
  D1 — Local-to-global burden (APS doctrine in Adequacy language).

  **Strata:** `apsRealizationLayerFromIff` (`ReflexiveArchitecture.Instances.FromAPS`);
  composition exactness entry point `composition_from_tracking_and_gluing` is in
  `ReflexiveArchitecture.Middle.CompositionExactness` (SPEC_001).
-/

import AdequacyArchitecture.Core.Basic
import ReflexiveArchitecture.Instances.FromAPS

universe u

namespace AdequacyArchitecture.LocalGlobal

open ReflexiveArchitecture

/-- Finite tracking in Strata’s middle layer (APS “local” side). -/
def LocallyTrackable (S : Type u) [M : Middle.RealizationLayer S] : Prop :=
  M.HasFiniteTracking

/-- Lawful gluing in Strata’s middle layer (APS “global” prerequisite). -/
def GlobalRequiresGluing (S : Type u) [M : Middle.RealizationLayer S] : Prop :=
  M.HasGluing

/-- Strata `RealizationLayer` obtained directly from the tracking∧gluing ↔ composition biconditional. -/
@[reducible]
def realizationLayerFromTrackingGluingIff (S : Type u)
    (hasFiniteTracking hasGluing iCompIdx iRecIdx : Prop)
    (iff_proof : iCompIdx ↔ hasFiniteTracking ∧ hasGluing) :
    Middle.RealizationLayer S :=
  Instances.apsRealizationLayerFromIff S hasFiniteTracking hasGluing iCompIdx iRecIdx iff_proof

/-- Such a middle layer always exists once the biconditional is given. -/
theorem nonempty_realization_layer_of_iff (S : Type u)
    (hasFiniteTracking hasGluing iCompIdx iRecIdx : Prop)
    (iff_proof : iCompIdx ↔ hasFiniteTracking ∧ hasGluing) :
    Nonempty (Middle.RealizationLayer S) :=
  ⟨realizationLayerFromTrackingGluingIff S hasFiniteTracking hasGluing iCompIdx iRecIdx iff_proof⟩

end AdequacyArchitecture.LocalGlobal
