/-
  Faithful APS middle layer from the **cross-corpus** `LinkedArchitecture` instance
  (`ReflexiveArchitecture.Instances.CrossCorpusInstance`).

  Strata does not yet ship a separate `ConcreteFromAPS` like NEMS/IC; the EPIC cross-corpus middle
  layer is a standard `RealizationLayer` with `comp_iff_finiteTracking_and_gluing` proved by `simp`.
  Carrier `Unit` matches the abstract barrier–linked construction; full **`LinkedArchitecture`**
  packaging: `Instances/LinkedLayer.lean`. It is **not** the `Fin 2` toy corridor — see
  `CorpusDischarge` / `apsCorpusRealizationLayer` for that track. **Two-point relocation packaging**
  (`UnifiedCarrierMorphisms` `not_exists_distinct_pair_faithful_aps_middle`) **cannot** use distinct indices on
  `Unit` — see `SPEC_024_NM1` § APS obstruction.
-/

import ReflexiveArchitecture.Instances.CrossCorpusInstance

namespace AdequacyArchitecture.Instances

open ReflexiveArchitecture
open ReflexiveArchitecture.Instances

@[reducible]
def faithfulAPSCrossCorpusRealizationLayer : Middle.RealizationLayer Unit :=
  crossCorpusMiddle

theorem nonempty_faithful_aps_cross_corpus_middle_layer :
    Nonempty (Middle.RealizationLayer Unit) :=
  ⟨faithfulAPSCrossCorpusRealizationLayer⟩

end AdequacyArchitecture.Instances
