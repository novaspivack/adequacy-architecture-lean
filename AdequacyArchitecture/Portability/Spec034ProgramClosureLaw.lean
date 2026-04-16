/-
  Program closure law (M1 / M2 / Step 4 Lean packaging).

  Canonical packaging for the termination doctrine summarized as **`PROGRAM_CLOSED`** below.

  * **M1 (positive):** certified structural data (frontier row, compare-pullback representation, or FE-4 ladder) ⇒
    **`AbsoluteFrontierRawS1`** for the relevant **`(P,B)`** — **not** unconstrained **`∀P,B`**.
  * **M2 (boundary):** explicit **no-go** for deducing **`AbsoluteFrontierRawS1`** for **arbitrary** **`P,B`** from ridge
    data alone on the corpus carrier.
  * **Step 4 (honesty):** native **`HFinal`** on **`icNemsSpineCompressionCarrier`** is **iff** the full **`HFinal`**
    spine checklist on that type — no silent gap (see **`ICNativeOuterClosure.lean`**).
-/

import AdequacyArchitecture.Portability.AbsoluteFrontierEarnedToy
import AdequacyArchitecture.Portability.CertifiedFrontierRow
import AdequacyArchitecture.Portability.CorpusConditionalRidgeFrontier
import AdequacyArchitecture.Portability.SummitRowRepresentation
import AdequacyArchitecture.Instances.ICNativeOuterClosure

universe u

namespace AdequacyArchitecture.Portability.Spec034ProgramClosureLaw

open AdequacyArchitecture
open AdequacyArchitecture.Instances
open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open AdequacyArchitecture.Portability

variable {α γ : Type u}

/-! ## M1 — certified representability ⇒ frontier consequence -/

/-- **SPEC_034 M1a** — certified frontier row ⇒ **`AbsoluteFrontierRawS1`** for **`lawful.P`**, **`lawful.B`**. -/
theorem M1_from_certifiedFrontierRow (row : CertifiedFrontierRow α) :
    AbsoluteFrontierRawS1 row.lawful.P row.lawful.B :=
  absoluteFrontierRawS1_of_certifiedFrontierRow row

/-- **SPEC_034 M1b** — valid **`CertifiedFrontierRepresentation`** pullback display ⇒ **`AbsoluteFrontierRawS1`** on **`γ`**. -/
theorem M1_from_validCertifiedFrontierRepresentation {P : AdequacyPredicates γ} {B : BurdenPredicates γ}
    (repr : CertifiedFrontierRepresentation γ α) (h : repr.IsPullbackDisplay P B) :
    AbsoluteFrontierRawS1 P B :=
  absoluteFrontierRawS1_of_valid_certifiedFrontierRepresentation repr h

/-- **SPEC_034 M1c** — FE-4 earned ladder **A–F** in one conjunction (**SPEC_029** / **`AbsoluteFrontierEarnedToy`**). -/
abbrev M1_earnedFrontierLadder_bundle :=
  fe4_earned_absoluteFrontierRawS1_ladder_bundle

/-- Parallel **Rung F** cite via **SPEC_033** gate (same **`Prop`** as **SPEC_031** pullback lemma — **`proof_irrel`**). -/
abbrev M1_earned_rungF_via_rl9_gate :=
  fe4_earned_absoluteFrontierRawS1_ic_native_compression_cs3_pullback_via_rl9_gate

/-! ## M2 — sharp impossibility boundary (paired with M1) -/

/-- **SPEC_034 M2a** — **`RidgeBridgeable`** at corpus **`𝔠₀`** does **not** entail **`AbsoluteFrontierRawS1`** for arbitrary **`P,B`**. -/
abbrev M2_obstruction_ridgeBridgeable_arbitraryPair :=
  not_forall_ridgeBridgeable_corpus_implies_absoluteFrontierRawS1_arbitrary_pair

/-- **SPEC_034 M2b** — same failure with the **stronger** antecedent **`RidgeCascadeWitness`**. -/
abbrev M2_obstruction_ridgeCascadeWitness_arbitraryPair :=
  not_forall_ridgeCascadeWitness_corpus_implies_absoluteFrontierRawS1_arbitrary_pair

/-! ## Step 4 — native IC carrier / `HFinal` checklist -/

/--
**SPEC_034 Step 4.** Nonempty **`HFinal`** on **`icNemsSpineCompressionCarrier`** iff full completed stratified spine +
**`(P,rcp)`** + ridge witness + non-flat (**`ic_phase1_nonempty_hfinal_iff_spine_data`**). **Program closure** documents the
paired **Stage D** resolution pack; **constructing** this spine **natively** on **`CompressionArchitecture …`** remains
**post-program** (**034 §XV**).
-/
abbrev Step4_nativeIcHFinal_iff_spineChecklist :=
  ic_phase1_nonempty_hfinal_iff_spine_data

end AdequacyArchitecture.Portability.Spec034ProgramClosureLaw
