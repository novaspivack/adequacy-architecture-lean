/-
  **SPEC_032 — representation interface:** compare-pullback packaging for “external” **`(P,B)`** on a native
  carrier **`γ`** into a **host** **`CertifiedFrontierRow α`**.

  **Theorem:** if **`(P,B)`** *is* the compare pullback of the host lawful predicates along **`π : γ → α`**, then
  **`AbsoluteFrontierRawS1`** holds for **`(P,B)`** — by **`lawfulAdequacyArchitecture_pullbackAlongCompare`** +
  **`universal_irreducible_adequacy_lawful`** (**no** raw **`∀P,B`**, **no** native **`CertifiedFrontierRow γ`**).

  **Worked examples:** identity compare on **`CorpusStrataCarrier`** (NEMS **Level 1** row; **Level 2** non-vacuous-final /
  **IC CS-3 aligned** row); nontrivial compare in **`ICCompareRepresentationPullback.lean`** (CS-3 pullback).

  **Ceiling:** this API does **not** supply **`Nonempty (HFinal γ)`** / native summit witnesses — only 𝒞 lawfulness
  and the master theorem on the pullback row. Native Layer A packaging remains **frontier** (see AF-1 / IC Stage D).

  **Obstruction (compare collapse):** **`compareLiftAccountAlong`** along a **constant** **`π`** can identify distinct
  native accounts — see **`compareLiftAccountAlong_collapses_of_constant`**; rich **FE-3** / indexed structure along
  **`π`** is therefore **not** automatic from **`CertifiedFrontierRepresentation`** alone.

  **Obstruction (alignment):** without **`IsPullbackDisplay`**, the host certified row and **`π`** impose **no**
  connection between an arbitrary external **`(P,B)`** and **`AbsoluteFrontierRawS1`** — the display hypothesis is
  the honest gate (compare **`CorpusConditionalRidgeFrontier`** for ridge-alone shortcuts).

  **SPEC_032 Stage B — injective compare:** **`HasInjectiveCompare`** (**`Function.Injective π`**) ⇒
  **`compareLiftAccountAlong π`** is injective (**`compareLiftAccountAlong_injective_of_repr_injective`**), matching
  functorial account discipline needed before any **FE-3 / indexed** story along **`π`**. **Constant** corpus compare
  (**IC CS-3**) **fails** injectivity — see **`icCs3CertifiedFrontierRepresentation_not_injectiveCompare`**.

  **SPEC_032 Stage C2 — NEMS composition boundary:** functorial FE-3 pullback along morphisms into the **bundle** side is
  **`indexedPhantomCertificateOps_pullbackAlongDom`** (+ NEMS **`haltingAnchoredNems_forgetful_indexedPhantomOps_pullbackAlongDom`**).
  Relating that to **`π`** needs **Law X** **`NemsFe3SummitBundleCompareSection`** (**`Instances/RepresentationNemsStageC2`**);
  **`HasInjectiveCompare`** does **not** supply **`proj`**.

  **SPEC_032 Phase D v4 — alignment:** **`isPullbackDisplay_iff_pulledBackLawful_eq`** re-expresses **`IsPullbackDisplay`**
  as **`repr.pulledBackLawful`**’s **`P,B`** components (**𝒞 pullbacks** still **do not** imply a bundle **`proj`**). APS middle
  parallel: **`Instances/RepresentationApsStageC2`** (**`ApsFe3MiddleBundleCompareSection`**).

  **Phase D v5 — carrier bridge:** NEMS **`nemsFe3IndexedPhantomOps_pullbackAlongDom_lawX_carrier_bridge`** (and APS dual) = FE-3 on **`γ`**
  via **`pullbackAlongDom (σ.proj ∘ i)`** = two-stage pullback for explicit **`i : γ → B_γ`** — **not** **`repr.π`**.

  **Phase D v6 — compare triangle (declared):** **`Instances/NemsSummitCarrierBridge`** — **`NemsSummitCarrierBridgeCompareAlignment`**
  + **`nemsFe3IndexedPhantomOps_pullbackAlongDom_align_factors_through_compare_then_host`**; **`BranchGenericSemanticTransport`**
  **`indexedPhantomCertificateOps_pullbackAlongDom_congr_dom`**. Note **`SPEC_032_PI1`**.

  **Phase D v7 — section-aware pack:** **`nemsSummitSectionAware_pack_isPullback_bridge_v5_forgetfulOnCarrier`** (+ variants). Note **`SPEC_032_SA1`**.
-/

import AdequacyArchitecture.Lawful.ComparePullback
import AdequacyArchitecture.Lawful.FinalConditionalSummit
import AdequacyArchitecture.Lawful.LawfulStructures
import AdequacyArchitecture.Portability.CertifiedFrontierRow

universe u

namespace AdequacyArchitecture.Portability

open AdequacyArchitecture
open AdequacyArchitecture.Instances
open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit

variable {γ α : Type u}

/--
**Representation datum:** a compare map **`γ → α`** and a **host** certified frontier row on **`α`**.

Advisor alias: prefer this name when emphasizing “summit row as representation target.”
-/
structure CertifiedFrontierRepresentation (γ α : Type u) where
  π : γ → α
  certified : CertifiedFrontierRow α

abbrev SummitRowRepresentation := CertifiedFrontierRepresentation

namespace CertifiedFrontierRepresentation

/--
**SPEC_032 Stage B:** compare map is **injective** — native accounts do not collide in **α** under **`π`**.
Necessary (not sufficient) for functorial **FE-3** / reindex discipline along **`π`**.
-/
abbrev HasInjectiveCompare (repr : CertifiedFrontierRepresentation γ α) : Prop :=
  Function.Injective repr.π

theorem compareLiftAccountAlong_injective_of_repr_injective (repr : CertifiedFrontierRepresentation γ α)
    (h : repr.HasInjectiveCompare) :
    Function.Injective (compareLiftAccountAlong repr.π) :=
  compareLiftAccountAlong_injective_of_injective_pi h

/-- **`(P,B)`** is the displayed compare pullback of the host lawful **𝒞** pair along **`repr.π`**. -/
def IsPullbackDisplay (repr : CertifiedFrontierRepresentation γ α) (P : AdequacyPredicates γ)
    (B : BurdenPredicates γ) : Prop :=
  P = repr.certified.lawful.P.pullbackAlongCompare repr.π ∧
    B = repr.certified.lawful.B.pullbackAlongCompare repr.π

/-- Auxiliary: the 𝒞 row carried by **`γ`** in the representation proof. -/
abbrev pulledBackLawful (repr : CertifiedFrontierRepresentation γ α) : LawfulAdequacyArchitecture γ :=
  lawfulAdequacyArchitecture_pullbackAlongCompare repr.π repr.certified.lawful

theorem pulledBackLawful_eq_of_isPullbackDisplay (repr : CertifiedFrontierRepresentation γ α)
    {P : AdequacyPredicates γ} {B : BurdenPredicates γ} (h : repr.IsPullbackDisplay P B) :
    repr.pulledBackLawful.P = P ∧ repr.pulledBackLawful.B = B := by
  rcases h with ⟨hP, hB⟩
  exact ⟨hP.symm, hB.symm⟩

/--
  **SPEC_032 Phase D (alignment):** **`IsPullbackDisplay`** is **exactly** the statement that the displayed **`(P,B)`**
  **are** the **`𝒞`** components of **`repr.pulledBackLawful`** — i.e. compare-pullback lawfulness **determines** the row
  on **`γ`**, while **Law X** / FE-3 **`proj : B_γ → Bundle`** is **extra** morphism data (**Stage C2** boundary).

  So **`pulledBackLawful`** alone fixes **`P,B`** but implies **nothing** about **NEMS** **`HaltingAnchoredFaithfulSummitMasterBundle`**
  maps.
-/
theorem isPullbackDisplay_iff_pulledBackLawful_eq (repr : CertifiedFrontierRepresentation γ α)
    (P : AdequacyPredicates γ) (B : BurdenPredicates γ) :
    repr.IsPullbackDisplay P B ↔ repr.pulledBackLawful.P = P ∧ repr.pulledBackLawful.B = B := by
  constructor
  · exact pulledBackLawful_eq_of_isPullbackDisplay repr
  · rintro ⟨hP, hB⟩
    refine And.intro ?_ ?_
    · simpa [pulledBackLawful, lawfulAdequacyArchitecture_pullbackAlongCompare] using hP.symm
    · simpa [pulledBackLawful, lawfulAdequacyArchitecture_pullbackAlongCompare] using hB.symm

end CertifiedFrontierRepresentation

/--
**Representation consequence:** compare-aligned **`(P,B)`** on **`γ`** inherits **RawS1** from the **host** 𝒞 row.

**Proof core:** **`lawfulAdequacyArchitecture_pullbackAlongCompare`** (**SPEC_031**) + **`MasterTheorem`**.
-/
theorem absoluteFrontierRawS1_of_valid_certifiedFrontierRepresentation {γ α : Type u}
    {P : AdequacyPredicates γ} {B : BurdenPredicates γ} (repr : CertifiedFrontierRepresentation γ α)
    (h : repr.IsPullbackDisplay P B) :
    AbsoluteFrontierRawS1 P B := by
  rcases h with ⟨hP, hB⟩
  rw [hP, hB]
  exact universal_irreducible_adequacy_lawful (lawfulAdequacyArchitecture_pullbackAlongCompare repr.π repr.certified.lawful)

/-- Advisor alias (same proof as **`absoluteFrontierRawS1_of_valid_certifiedFrontierRepresentation`**). -/
theorem absoluteFrontierRawS1_of_valid_summitRowRepresentation {γ α : Type u}
    {P : AdequacyPredicates γ} {B : BurdenPredicates γ} (repr : CertifiedFrontierRepresentation γ α)
    (h : repr.IsPullbackDisplay P B) :
    AbsoluteFrontierRawS1 P B :=
  absoluteFrontierRawS1_of_valid_certifiedFrontierRepresentation repr h

/-! ## Worked example — corpus host, **identity** compare (defeq to host **`P,B`**) -/

/-- Host = native carrier; **`π = id`** re-types the NEMS Level-1 certified row as a pullback display. -/
def certifiedFrontierRepresentation_corpus_nems_level1_id :
    CertifiedFrontierRepresentation CorpusStrataCarrier CorpusStrataCarrier where
  π := id
  certified := certifiedFrontierRow_corpus_nems_level1

theorem certifiedFrontierRepresentation_corpus_nems_level1_id_hasInjectiveCompare :
    certifiedFrontierRepresentation_corpus_nems_level1_id.HasInjectiveCompare := fun _ _ h => h

theorem certifiedFrontierRepresentation_corpus_nems_level1_id_isPullbackDisplay :
    certifiedFrontierRepresentation_corpus_nems_level1_id.IsPullbackDisplay corpusNemsFin2Adequacy
      corpusNemsFin2Burden := by
  refine And.intro ?_ ?_
  · show corpusNemsFin2Adequacy = corpusNemsFin2LawfulArchitecture.P.pullbackAlongCompare id
    rw [AdequacyPredicates.pullbackAlongCompare_id]
    rfl
  · show corpusNemsFin2Burden = corpusNemsFin2LawfulArchitecture.B.pullbackAlongCompare id
    rw [BurdenPredicates.pullbackAlongCompare_id]
    rfl

theorem absoluteFrontierRawS1_corpus_nems_level1_via_summitRowRepresentation :
    AbsoluteFrontierRawS1 corpusNemsFin2Adequacy corpusNemsFin2Burden :=
  absoluteFrontierRawS1_of_valid_certifiedFrontierRepresentation
    certifiedFrontierRepresentation_corpus_nems_level1_id
    certifiedFrontierRepresentation_corpus_nems_level1_id_isPullbackDisplay

/-! ### Corpus **Level 2 NV** (non-vacuous final) — identity compare, **IC CS-3 aligned** predicates -/

/-- Same as Level-1 id packaging, with **`certifiedFrontierRow_corpus_nems_level2_nv`** ( **`corpusNemsFin2NvLawfulArchitecture`** ). -/
def certifiedFrontierRepresentation_corpus_nems_level2_nv_id :
    CertifiedFrontierRepresentation CorpusStrataCarrier CorpusStrataCarrier where
  π := id
  certified := certifiedFrontierRow_corpus_nems_level2_nv

theorem certifiedFrontierRepresentation_corpus_nems_level2_nv_id_hasInjectiveCompare :
    certifiedFrontierRepresentation_corpus_nems_level2_nv_id.HasInjectiveCompare := fun _ _ h => h

theorem certifiedFrontierRepresentation_corpus_nems_level2_nv_id_isPullbackDisplay :
    certifiedFrontierRepresentation_corpus_nems_level2_nv_id.IsPullbackDisplay
      icCorpusAlignedNonVacuousFinalAdequacy icCorpusAlignedBurden := by
  refine And.intro ?_ ?_
  · show icCorpusAlignedNonVacuousFinalAdequacy =
        corpusNemsFin2NvLawfulArchitecture.P.pullbackAlongCompare id
    rw [AdequacyPredicates.pullbackAlongCompare_id]
    rfl
  · show icCorpusAlignedBurden = corpusNemsFin2NvLawfulArchitecture.B.pullbackAlongCompare id
    rw [BurdenPredicates.pullbackAlongCompare_id]
    rfl

theorem absoluteFrontierRawS1_corpus_nems_level2_nv_via_summitRowRepresentation :
    AbsoluteFrontierRawS1 icCorpusAlignedNonVacuousFinalAdequacy icCorpusAlignedBurden :=
  absoluteFrontierRawS1_of_valid_certifiedFrontierRepresentation
    certifiedFrontierRepresentation_corpus_nems_level2_nv_id
    certifiedFrontierRepresentation_corpus_nems_level2_nv_id_isPullbackDisplay

end AdequacyArchitecture.Portability
