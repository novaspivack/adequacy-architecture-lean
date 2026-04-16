/-
  **SPEC_029 FE-4 — corpus `𝔠₀` + `RidgeBridgeable` / `RidgeCascadeWitness` vs `AbsoluteFrontierRawS1`.**

  * **Positive (parameterized Layer A):** `Instances/CorpusPhaseC.lean` —
    **`corpus_phaseC_master_stratified_adequacy_cascade_at`** — full **`MasterStratifiedAdequacyCascadeAt`**
    at corpus **`𝔠₀`** for **any** **`(P,rcp)`** with **non-flat**, because **`RidgeCascadeWitness 𝔠₀`** is **proved**.
  * **Obstruction:** structural **`RidgeBridgeable`** (or the **full** ridge witness) at **`𝔠₀`** does **not**
    entail **`AbsoluteFrontierRawS1 P B`** for **arbitrary** `P,B` — **𝒞** / **B1** is **independent** (Stage B+
    counterexample on the **same** carrier).
-/

import AdequacyArchitecture.Instances.CorpusLawfulRepresentation
import AdequacyArchitecture.Lawful.FinalConditionalSummit
import AdequacyArchitecture.Portability.S1ShapeNecessityCounterexample

namespace AdequacyArchitecture.Portability

open AdequacyArchitecture
open AdequacyArchitecture.Instances
open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open AdequacyArchitecture.Summit

/--
**FE-4 sharp obstruction:** even with **`RidgeBridgeable`**
holding at the corpus **`𝔠₀`**, **`AbsoluteFrontierRawS1 P B`** can **fail** for **wild** `P,B` (**no** lawful /
**𝒞** link). Missing law: **`LawfulAdequacyArchitecture` / `forces_each`** at the chosen pair — not repairable
from **`RidgeBridgeable`** alone.
-/
theorem not_forall_ridgeBridgeable_corpus_implies_absoluteFrontierRawS1_arbitrary_pair :
    ¬ (∀ (P : AdequacyPredicates CorpusStrataCarrier) (B : BurdenPredicates CorpusStrataCarrier),
        RidgeBridgeable corpusToyCompletedStratifiedLawfulAdequacyArchitecture → AbsoluteFrontierRawS1 P B) := by
  intro h
  refine not_absoluteFrontierRawS1Counterexample
    (h (s1CounterexampleReprOnlyAdequacy CorpusStrataCarrier) (s1CounterexampleEmptyBurden CorpusStrataCarrier)
      corpus_toy_ridge_bridgeable)

/--
Same obstruction with the **stronger** antecedent **`RidgeCascadeWitness`** (also **unconditional** at **`𝔠₀`**).
-/
theorem not_forall_ridgeCascadeWitness_corpus_implies_absoluteFrontierRawS1_arbitrary_pair :
    ¬ (∀ (P : AdequacyPredicates CorpusStrataCarrier) (B : BurdenPredicates CorpusStrataCarrier),
        RidgeCascadeWitness corpusToyCompletedStratifiedLawfulAdequacyArchitecture → AbsoluteFrontierRawS1 P B) := by
  intro h
  refine not_absoluteFrontierRawS1Counterexample
    (h (s1CounterexampleReprOnlyAdequacy CorpusStrataCarrier) (s1CounterexampleEmptyBurden CorpusStrataCarrier)
      corpus_toy_ridge_cascade_witness)

end AdequacyArchitecture.Portability
