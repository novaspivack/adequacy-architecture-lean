/-
  Summit S1 — target shape over arbitrary `P,B` vs **proved** for `LawfulAdequacyArchitecture` (SPEC_008).

  **Theorem:** `AdequacyArchitecture.Lawful.universal_irreducible_adequacy_lawful`.
  **Earned instances:** `AdequacyArchitecture.Toy.toy_universal_irreducible_adequacy`; summit/corpus ladder
  `Portability/AbsoluteFrontierEarnedToy.lean` (`fe4_earned_*`, ladder **A–F** incl. **`SPEC_031_ZK9`** pullback rung); NEMS Rows 1–2
  `corpusNemsFin2_universal_irreducible_adequacy` (`Instances/NEMSBridgeCoreRecord.lean`).
  **Over 𝒞 (abbrev + re-export):** `AdequacyArchitecture.Summit.SummitS1AtLawful`, `summitS1_at_lawful` (`Summit/SummitOverClass.lean`; SPEC_012).
  **SPEC_030 Stage B minimal gate:** `Portability/CertifiedFrontierRow.lean` — **`S1LawfulFrontierRow`** + **`absoluteFrontierRawS1_of_s1LawfulFrontierRow`** (**defeq** this shape). **SPEC_030 B+ counterexample:** `Portability/S1ShapeNecessityCounterexample.lean` — same **def** can fail **without** 𝒞.   **SPEC_031_ZK9 Stage A:** **`icNativeCompression_cs3_pullback_universal_irreducible`** — **native** IC compression carrier **via** compare pullback (not corpus-named **`P,B`** literally).
  **SPEC_032_RQ2:** **`Portability/SummitRowRepresentation.lean`** — **`CertifiedFrontierRepresentation`** + **`IsPullbackDisplay`** ⇒ **`absoluteFrontierRawS1_of_valid_certifiedFrontierRepresentation`**; **Stage B:** **`HasInjectiveCompare`** / injective **compare-lift** vs IC **`ic_compareToCorpus_not_injective`**; IC RawS1 example **`icNativeCompression_absoluteFrontierRawS1_cs3_pullback_via_representation`**.
-/

import AdequacyArchitecture.Core.Basic

universe u

namespace AdequacyArchitecture.Summit

/-- Target shape (same as summit S1). For raw `P,B` this is **not** proved; for **lawful** architectures it is a theorem. -/
def UniversalIrreducibleAdequacyConjecture (α : Type u) (P : AdequacyPredicates α) (B : BurdenPredicates α) : Prop :=
  ∀ (m : AdeqMode) (A : Account α), P.adeq m A → ∃ (m' : BurdenMode), B.burden m' A

end AdequacyArchitecture.Summit
