/-
  **SPEC_028 EX-8** — bounded **Stage F** portability pointer: **corpus Strata corridor** on **`CorpusStrataCarrier`**.

  Authoritative proofs live in **`Instances/CorpusDischarge.lean`** (**SPEC_013**). This module gives
  **externalization** readers a single **`Portability`** import path to the “three layers inhabited on `Fin 2`” fact. -/
import AdequacyArchitecture.Instances.CorpusDischarge

namespace AdequacyArchitecture.Portability

open ReflexiveArchitecture
open AdequacyArchitecture.Instances

/-- Shared **SPEC_013** index carrier (alias for search / cross-reference). -/
abbrev corpusStrataIndexCarrier := CorpusStrataCarrier

/-- **Bounded F slice:** NEMS outer + APS middle + IC inner are all **inhabited** on the corpus carrier. -/
theorem portability_strata_corridor_bundle :
    Nonempty (Outer.ReflexiveLayer CorpusStrataCarrier) ∧
      Nonempty (Middle.RealizationLayer CorpusStrataCarrier) ∧
      Nonempty (Inner.CertificationLayer CorpusStrataCarrier) :=
  nonempty_strata_corridor_on_corpus_carrier

end AdequacyArchitecture.Portability
