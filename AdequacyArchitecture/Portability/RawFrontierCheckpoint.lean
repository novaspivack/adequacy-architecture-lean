/-
  **SPEC_029_FR1 — FE-4 (proved checkpoint):** one **machine-checked** conjunction packaging the **bounded**
  corpus carrier (`Fin 2` / `CorpusStrataCarrier`) strata corridor with **SPEC_013 Phase C (partial)** ridge
  consequences at the corpus-linked completed stratified instance.

  This is **not** raw **`∀P,B`** or **`AbsoluteFrontierRawS1`**; it is honest **proved progress** toward the
  “conditional ridge at named `𝔠`” column in **`RAW_FRONTIER_SHARP_TARGETS.md`**.

  **Authoritative components:** **`CorpusDischarge`** (nonempty layers), **`CorpusPhaseC`** (Phase C pipeline).
-/

import AdequacyArchitecture.Instances.CorpusDischarge
import AdequacyArchitecture.Instances.CorpusPhaseC

namespace AdequacyArchitecture.Portability

open AdequacyArchitecture.Instances
open AdequacyArchitecture.Lawful
open ReflexiveArchitecture

/-- **FE-4 checkpoint** — explicit witness tuple (so conjunction projections compute for glue lemmas). -/
def fe4_corpus_fin2_frontend_strata_nonempty_and_phaseC_ridge_proof :
    Nonempty (Outer.ReflexiveLayer CorpusStrataCarrier) ∧
      Nonempty (Middle.RealizationLayer CorpusStrataCarrier) ∧
      Nonempty (Inner.CertificationLayer CorpusStrataCarrier) ∧
      MasterStratifiedAdequacyCascadeRidgeAt corpusToyCompletedStratifiedLawfulAdequacyArchitecture ∧
      CarrierPatternInducesRouteConstraintAt corpusToyCompletedStratifiedLawfulAdequacyArchitecture :=
  ⟨nonempty_nems_corpus_outer_layer, nonempty_aps_corpus_middle_layer, nonempty_ic_corpus_certification_layer,
    corpus_phaseC_master_stratified_adequacy_cascade_ridge,
    corpus_phaseC_carrier_pattern_from_ridgeBridgeable⟩

/-- **FE-4 checkpoint:** strata **`From*`** interfaces are inhabited on **`CorpusStrataCarrier`**, and the
    corpus-named toy `𝔠` satisfies **`RidgeCascadeWitness ⇒` master cascade ridge** and
    **`RidgeBridgeable ⇒` carrier-pattern route conjunct** (SPEC_012 packaging). -/
theorem fe4_corpus_fin2_frontend_strata_nonempty_and_phaseC_ridge :
    Nonempty (Outer.ReflexiveLayer CorpusStrataCarrier) ∧
      Nonempty (Middle.RealizationLayer CorpusStrataCarrier) ∧
      Nonempty (Inner.CertificationLayer CorpusStrataCarrier) ∧
      MasterStratifiedAdequacyCascadeRidgeAt corpusToyCompletedStratifiedLawfulAdequacyArchitecture ∧
      CarrierPatternInducesRouteConstraintAt corpusToyCompletedStratifiedLawfulAdequacyArchitecture :=
  fe4_corpus_fin2_frontend_strata_nonempty_and_phaseC_ridge_proof

/--
The **first three** conjuncts of **`fe4`** match the SPEC_013 **nonempty strata corridor**
(`Instances/CorpusDischarge.lean`): projections of **`fe4_corpus_fin2_frontend_strata_nonempty_and_phaseC_ridge_proof`**
are **`proof_irrel`**-equal to **`nonempty_strata_corridor_on_corpus_carrier`** (same proposition; same witness spine).
-/
theorem fe4_strata_prefix_eq_nonempty_strata_corridor_on_corpus_carrier :
    (⟨
      fe4_corpus_fin2_frontend_strata_nonempty_and_phaseC_ridge_proof.1,
      fe4_corpus_fin2_frontend_strata_nonempty_and_phaseC_ridge_proof.2.1,
      fe4_corpus_fin2_frontend_strata_nonempty_and_phaseC_ridge_proof.2.2.1,
    ⟩ : Nonempty (Outer.ReflexiveLayer CorpusStrataCarrier) ∧
        Nonempty (Middle.RealizationLayer CorpusStrataCarrier) ∧
        Nonempty (Inner.CertificationLayer CorpusStrataCarrier)) =
      nonempty_strata_corridor_on_corpus_carrier :=
  proof_irrel _ _

end AdequacyArchitecture.Portability
