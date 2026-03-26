/-
  **SPEC_026 — Phase 1 (IC native outer-closure).**

  **`ICBridgeCoreRecord` / `ICSummitRepresentation`** already package IC-native multiplicity with the **corpus**
  **`HFinal`**. This module records the **remaining** Phase-1 target: a **native** or **represented** lawful summit
  spine on **`CompressionArchitecture Unit _`**, not only on **`CorpusStrataCarrier`**.

  **Delivered here (honest primitives):**
  * named IC summit carrier (`icNemsSpineCompressionCarrier`);
  * **nontriviality** — two distinct `CompressionArchitecture` witnesses (`nems_spine_architecture_ne_altTerminal`);
  * **status** lemma tying that to a nonempty faithful **`Inner.CertificationLayer`** (via **`ICBridgeCoreRecord`**);
  * a minimal **`ICOuterClosureRepresentationCompare`** bundle (compare map only) — **TODO:** extend with
    predicate / ridge pullback laws once a functorial compare discipline is fixed.

  **Not claimed:** `HFinal icNemsSpineCompressionCarrier` or `CompletedStratifiedLawfulAdequacyArchitecture` on that
  carrier without new construction (see spec obstruction clause).
-/

import AdequacyArchitecture.Instances.CorpusDischarge
import AdequacyArchitecture.Instances.ICBridgeCoreRecord
import AdequacyArchitecture.Lawful.FinalConditionalSummit
import InfinityCompression.Meta.NEMSSpineAsArchitecture

namespace AdequacyArchitecture.Instances

open InfinityCompression.Meta
open ReflexiveArchitecture
open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit

/-- IC Phase-1 summit carrier: canonical NEMS spine as `CompressionArchitecture`. -/
abbrev icNemsSpineCompressionCarrier : Type :=
  CompressionArchitecture Unit nemsSpineChain.steps.length

theorem ic_nems_spine_compression_carrier_nontrivial :
    ∃ a b : icNemsSpineCompressionCarrier, a ≠ b :=
  ⟨nemsSpineChain.toArchitecture, nemsSpineChain_altTerminal.toArchitecture,
    nems_spine_architecture_ne_altTerminal⟩

theorem corpus_strata_two_distinct_indices : ∃ i j : CorpusStrataCarrier, i ≠ j :=
  ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide⟩

/--
Phase-1 **status**: native carrier is nontrivial **as architecture**, and the canonical host carries a nonempty
faithful certification layer (re-export of **`ICBridgeCoreRecord`**).
-/
theorem ic_phase1_native_multiplicity_status :
    (∃ a b : icNemsSpineCompressionCarrier, a ≠ b) ∧
      Nonempty (Inner.CertificationLayer icNemsSpineCompressionCarrier) :=
  ⟨ic_nems_spine_compression_carrier_nontrivial, ic_nonempty_faithful_canonical_certification_layer⟩

/--
Minimal compare-map hypothesis for a **representation morphism** into the corpus lawful carrier.

**SPEC_031_ZK9 (Stage A):** generic **`𝒞` pullback** along **`compareToCorpus`** is **`lawfulAdequacyArchitecture_pullbackAlongCompare`**
in **`Lawful/ComparePullback.lean`**; IC constant-compare packaging: **`icNativeCompressionLawfulArchitecture_cs3_pullback`**.

**TODO (later stages):** witnessed **`RidgeCascadeWitness`** / stratified **`𝔠.strat.compare`** alignment; **FE-3** transport.
-/
structure ICOuterClosureRepresentationCompare (β : Type) where
  compareToCorpus : β → CorpusStrataCarrier

/--
**Phase 1 — sharp checklist (obstruction shape).** A native `HFinal` on **`icNemsSpineCompressionCarrier`** is
equivalent to producing a **full** `CompletedStratifiedLawfulAdequacyArchitecture` on that type plus ridge + non-flat
at some `(P,rcp)` — the package exports **no** such `𝔠` today (only the corpus/toy spine on **`CorpusStrataCarrier`**).

So closing IC natively means **new** `𝔠` construction **or** a representation morphism + pullback laws
(`ICOuterClosureRepresentationCompare` TODO).
-/
theorem ic_phase1_nonempty_hfinal_iff_spine_data :
    Nonempty (HFinal icNemsSpineCompressionCarrier) ↔
      ∃ (𝔠 : CompletedStratifiedLawfulAdequacyArchitecture icNemsSpineCompressionCarrier)
        (P : AdequacyPredicates icNemsSpineCompressionCarrier)
        (rcp : RouteConstraintProfile icNemsSpineCompressionCarrier) (_ : RidgeCascadeWitness 𝔠)
        (_ : NonFlatFinalityFromRouteConstraintFor P rcp), True :=
  HFinal.nonempty_iff

end AdequacyArchitecture.Instances
