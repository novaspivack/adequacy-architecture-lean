/-
  **Theorem-fed** Strata middle layer from **indexed APS** (`APSMinimalInterface.Indexed.IndexedAPS`).

  * **Interpolation exactness** (`APSUniformization.Synthesis.aps_interpolation_exactness`):
    `HasICompIndexed aps ↔ HasFiniteTracking aps ∧ HasGluing aps` — the biconditional
    `ReflexiveArchitecture.Instances.apsRealizationLayerFromIff` expects.
  * **Corrected exactness** (`APSRecComp.ConditionalNecessity.corrected_exactness_iff`):
    `HasICompIndexed ↔ SmnTrackingForRep` — re-exported for cross-reference.

  Carrier for the Strata `RealizationLayer` is **`Unit`**: we fix one `aps : IndexedAPS` and
  record predicates at that instance (same pattern as `APSFaithful` on `Unit`).

  **Comparison with `Fin 2` corpus:** `CorpusDischarge.lean` uses toy biconditionals on `Fin 2`;
  account indices inject into `ℕ` (`Fin.val : Fin 2 → ℕ`), the usual domain of indexed APS codes.
  See `corpus_fin2_index_embedding` in `CorpusDischarge.lean`.
-/

import APSMinimalInterface.Indexed
import APSMinimalInterface.InterfaceLattice
import APSMinimalInterface.IndexedCountermodels
import APSRecComp.ConditionalNecessity
import APSUniformization.Synthesis
import ReflexiveArchitecture.Instances.FromAPS

namespace AdequacyArchitecture.Instances

open ReflexiveArchitecture
open ReflexiveArchitecture.Instances
open APSMinimalInterface
open APSRecComp
open APSUniformization

/-- Strata `RealizationLayer` for a fixed `aps`, using **proved** `aps_interpolation_exactness`. -/
@[reducible]
def indexedApsRealizationLayer (aps : IndexedAPS) : Middle.RealizationLayer Unit :=
  apsRealizationLayerFromIff Unit
    (HasFiniteTracking aps)
    (HasGluing aps)
    (HasICompIndexed aps)
    (HasIRecIndexed aps)
    (aps_interpolation_exactness aps)

/-- The minimal indexed APS from the countermodel library (comp may fail; exactness still applies). -/
@[reducible]
def minimalIndexedApsRealizationLayer : Middle.RealizationLayer Unit :=
  indexedApsRealizationLayer minimalIndexedAPS

theorem nonempty_minimal_indexed_aps_middle_layer :
    Nonempty (Middle.RealizationLayer Unit) :=
  ⟨minimalIndexedApsRealizationLayer⟩

/-- Re-export: **I_comp ↔ SmnTrackingForRep** (corrected exactness). -/
abbrev aps_corrected_exactness_iff := corrected_exactness_iff

/-- Re-export: **I_comp ↔ finite tracking ∧ gluing** (`∀ aps`, interpolation exactness). -/
abbrev aps_interpolation_exactness_named := aps_interpolation_exactness

end AdequacyArchitecture.Instances
