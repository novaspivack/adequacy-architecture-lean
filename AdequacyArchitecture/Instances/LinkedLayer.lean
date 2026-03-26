/-
  Strata **LinkedArchitecture** on **`Unit`** — the EPIC **cross-corpus** instance
  (`ReflexiveArchitecture.Instances.crossCorpusLinkedArchitecture`).

  Here `EnrichedIrreducibility ↔ ∃ T, InternalTheory T ∧ SemanticRemainder T` holds by the
  Strata **definitional** link (`Iff.rfl` on `BarrierProp`). This is the formal **linked layer**
  for “representation does not erase the represented” in the abstract barrier sense.

  **Honesty:** this is **not** the **`Fin 2`** corpus corridor (`CorpusDischarge.lean`), which uses
  separate `From*` instantiations on `CorpusStrataCarrier`. The linked architecture lives on
  **`Unit`** as in Strata `CrossCorpusInstance.lean`. **How this differs** from the faithful
  NEMS+IC **conjunction** (`FaithfulCorpusJoint` / `DirectCrossCorpusBridge`): see
  **`HonestyBridge.lean`**.
-/

import ReflexiveArchitecture.Bridge.LinkedArchitecture
import ReflexiveArchitecture.Instances.CrossCorpusInstance

namespace AdequacyArchitecture.Instances

open ReflexiveArchitecture
open ReflexiveArchitecture.Instances
open ReflexiveArchitecture.Bridge

/-- Strata `crossCorpusLinkedArchitecture`, exposed under Adequacy `Instances` naming. -/
abbrev linkedCorpusArchitecture : LinkedArchitecture Unit :=
  crossCorpusLinkedArchitecture

theorem nonempty_linked_corpus_architecture : Nonempty (LinkedArchitecture Unit) :=
  ⟨linkedCorpusArchitecture⟩

theorem linked_corpus_enriched_iff_remainder :
    linkedCorpusArchitecture.EnrichedIrreducibility ↔
      ∃ T, linkedCorpusArchitecture.InternalTheory T ∧
        linkedCorpusArchitecture.SemanticRemainder T :=
  linked_biconditional_unconditional (R := linkedCorpusArchitecture)

theorem linked_corpus_nonerasure_unconditional :
    linkedCorpusArchitecture.EnrichedIrreducibility :=
  crossCorpus_nonerasure_unconditional

end AdequacyArchitecture.Instances
