/-
  **SPEC_032 — representation interface:** compare-pullback packaging for “external” **`(P,B)`** on a native
  carrier **`γ`** into a **host** **`CertifiedFrontierRow α`**.

  **Theorem:** if **`(P,B)`** *is* the compare pullback of the host lawful predicates along **`π : γ → α`**, then
  **`AbsoluteFrontierRawS1`** holds for **`(P,B)`** — by **`lawfulAdequacyArchitecture_pullbackAlongCompare`** +
  **`universal_irreducible_adequacy_lawful`** (**no** raw **`∀P,B`**, **no** native **`CertifiedFrontierRow γ`**).

  **Worked examples:** identity compare on **`CorpusStrataCarrier`** (NEMS **Level 1** row; **Level 2** non-vacuous-final /
    **IC CS-3 aligned** row); **fiber swap** **`corpusStrataCarrierSwap`** on the **same** Level-2 NV certified host (**SPEC_035 Q1**);
    nontrivial compare in **`ICCompareRepresentationPullback.lean`** (CS-3 pullback).

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
  **SPEC_035 Program 1 / S1a — cleaving:** **`compareLiftAccountAlong_comp`** / **`pullbackAlongCompare_comp`** + **`CertifiedFrontierRepresentation.comp`**
  when an **inner** host row is **definitionally** the 𝒞-pullback of an **outer** host along **`outer.π`**.
  **SPEC_035 Q3 / S5 — parallel packaging:** **`pullbackDisplay_with_host_summitFE3`** (**native** RawS1 from display **∧** expanded
  **Stage C** joint law on the **host** — defeq to **`summitFE3_joint_semantic_law`** **`repr.certified.toSummitFE3`**) — **not** a
  collapse; **named:** **`pullbackDisplay_with_host_summitFE3_corpus_nems_level1_id`**, **`pullbackDisplay_with_host_summitFE3_corpus_nems_level2_nv_{id,swap}`**. See **`PROGRAM1_S5_MASTER_SWIPE_TEST`**.
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
open AdequacyArchitecture.Portability.BranchGenericSemanticTransport

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

/--
**SPEC_035 / S1a:** compose an **outer** representation (**`γ → α`**, host on **`α`**) with an **inner** (**`δ → γ`**) using
the **same** host **`CertifiedFrontierRow α`** — compare map **`outer.π ∘ inner.π`**.
-/
def comp {δ : Type u} (outer : CertifiedFrontierRepresentation γ α) (inner : CertifiedFrontierRepresentation δ γ) :
    CertifiedFrontierRepresentation δ α where
  π := outer.π ∘ inner.π
  certified := outer.certified

/--
**S1a cleaving:** when the **inner** certified row’s lawfulness is **exactly** the outer 𝒞-pullback
(`inner.host = outer.pulledBackLawful`), pullback **display** along **`inner.π`** is the same predicate as display for the
**composite** compare **`outer.π ∘ inner.π`** (by **`pullbackAlongCompare_comp`**).
-/
theorem isPullbackDisplay_comp_iff_of_pulledBackInner {δ : Type u} (outer : CertifiedFrontierRepresentation γ α)
    (inner : CertifiedFrontierRepresentation δ γ) {P : AdequacyPredicates δ} {B : BurdenPredicates δ}
    (hpull :
      inner.certified.lawful =
        lawfulAdequacyArchitecture_pullbackAlongCompare outer.π outer.certified.lawful) :
    inner.IsPullbackDisplay P B ↔ (comp outer inner).IsPullbackDisplay P B := by
  constructor
  · rintro ⟨hP, hB⟩
    refine And.intro ?_ ?_
    · simpa [IsPullbackDisplay, comp, hpull, lawfulAdequacyArchitecture_pullbackAlongCompare,
        AdequacyPredicates.pullbackAlongCompare_comp] using hP
    · simpa [IsPullbackDisplay, comp, hpull, lawfulAdequacyArchitecture_pullbackAlongCompare,
        BurdenPredicates.pullbackAlongCompare_comp] using hB
  · rintro ⟨hP, hB⟩
    refine And.intro ?_ ?_
    · simpa [IsPullbackDisplay, comp, hpull, lawfulAdequacyArchitecture_pullbackAlongCompare,
        AdequacyPredicates.pullbackAlongCompare_comp] using hP
    · simpa [IsPullbackDisplay, comp, hpull, lawfulAdequacyArchitecture_pullbackAlongCompare,
        BurdenPredicates.pullbackAlongCompare_comp] using hB

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

/--
**SPEC_035 Program 1 / Q3–S5 (master-swipe packaging):** under **`IsPullbackDisplay`**, the **native** **`(P,B)`** pair
inherits **`AbsoluteFrontierRawS1`** (**S1a** / **`U_pullback`**), while the **host** certified row still satisfies the
**Stage C** joint semantic law (**`summitFE3_joint_semantic_law`**) on **`α`** — **independently** of **`h`**.

This is **not** a collapse of the two mechanisms: **`summitFE3_joint_semantic_law`** is about the **host**
**`SummitFE3SemanticPackage`**, not a **native** **`HFinal γ`** statement. Unification (**`U*`** compression) would need
extra morphism data (see **`PROGRAM1_S5_MASTER_SWIPE_TEST`** / **`GenericSemanticSummitLift`**).
-/
theorem pullbackDisplay_with_host_summitFE3 {γ α : Type u} {P : AdequacyPredicates γ} {B : BurdenPredicates γ}
    {repr : CertifiedFrontierRepresentation γ α} (h : repr.IsPullbackDisplay P B) :
    (AbsoluteFrontierRawS1 P B) ∧
      (MasterStratifiedAdequacyCascadeAt repr.certified.summitTagged.toHFinal.𝔠
          repr.certified.summitTagged.toHFinal.P repr.certified.summitTagged.toHFinal.rcp ∧
        ForgetfulIndexedCoherent repr.certified.fe3.ops ∧
        ForgetfulAgreementInjects repr.certified.fe3.ops) := by
  refine And.intro ?_ ?_
  · exact absoluteFrontierRawS1_of_valid_certifiedFrontierRepresentation repr h
  · exact certifiedFrontierRow_summitFE3_joint repr.certified

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

/--
**SPEC_035 Program 1 / Q3–S5:** **`pullbackDisplay_with_host_summitFE3`** for **corpus Level-1** (**Fin 2** corridor, **vacuous-final** summit packaging) with **`π = id`**.

Completes the **Level-1** parallel to **`pullbackDisplay_with_host_summitFE3_corpus_nems_level2_nv_id`** — same **host joint** pattern, **different** native **`(P,B)`** (**`corpusNemsFin2*`** vs **IC-aligned** Level-2 NV).
-/
theorem pullbackDisplay_with_host_summitFE3_corpus_nems_level1_id :
    (AbsoluteFrontierRawS1 corpusNemsFin2Adequacy corpusNemsFin2Burden) ∧
      (MasterStratifiedAdequacyCascadeAt certifiedFrontierRow_corpus_nems_level1.summitTagged.toHFinal.𝔠
          certifiedFrontierRow_corpus_nems_level1.summitTagged.toHFinal.P
          certifiedFrontierRow_corpus_nems_level1.summitTagged.toHFinal.rcp ∧
        ForgetfulIndexedCoherent certifiedFrontierRow_corpus_nems_level1.fe3.ops ∧
        ForgetfulAgreementInjects certifiedFrontierRow_corpus_nems_level1.fe3.ops) :=
  pullbackDisplay_with_host_summitFE3 certifiedFrontierRepresentation_corpus_nems_level1_id_isPullbackDisplay

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

/--
**SPEC_035 Program 1 / Q3–S5:** **`pullbackDisplay_with_host_summitFE3`** for **corpus Level-2 NV** with **`π = id`**
(**baseline** beside **`pullbackDisplay_with_host_summitFE3_corpus_nems_level2_nv_swap`**).
-/
theorem pullbackDisplay_with_host_summitFE3_corpus_nems_level2_nv_id :
    (AbsoluteFrontierRawS1 icCorpusAlignedNonVacuousFinalAdequacy icCorpusAlignedBurden) ∧
      (MasterStratifiedAdequacyCascadeAt certifiedFrontierRow_corpus_nems_level2_nv.summitTagged.toHFinal.𝔠
          certifiedFrontierRow_corpus_nems_level2_nv.summitTagged.toHFinal.P
          certifiedFrontierRow_corpus_nems_level2_nv.summitTagged.toHFinal.rcp ∧
        ForgetfulIndexedCoherent certifiedFrontierRow_corpus_nems_level2_nv.fe3.ops ∧
        ForgetfulAgreementInjects certifiedFrontierRow_corpus_nems_level2_nv.fe3.ops) :=
  pullbackDisplay_with_host_summitFE3 certifiedFrontierRepresentation_corpus_nems_level2_nv_id_isPullbackDisplay

/-! ### Corpus Level 2 NV — **fiber swap** compare (SPEC_035 Q1 / nontrivial **S1a** display) -/

/-- Same certified host row; **`π = corpusStrataCarrierSwap`** (involutive, injective, **≠ `id`**). -/
def certifiedFrontierRepresentation_corpus_nems_level2_nv_swap :
    CertifiedFrontierRepresentation CorpusStrataCarrier CorpusStrataCarrier where
  π := corpusStrataCarrierSwap
  certified := certifiedFrontierRow_corpus_nems_level2_nv

theorem certifiedFrontierRepresentation_corpus_nems_level2_nv_swap_hasInjectiveCompare :
    certifiedFrontierRepresentation_corpus_nems_level2_nv_swap.HasInjectiveCompare :=
  corpusStrataCarrierSwap_injective

theorem certifiedFrontierRepresentation_corpus_nems_level2_nv_swap_isPullbackDisplay :
    certifiedFrontierRepresentation_corpus_nems_level2_nv_swap.IsPullbackDisplay
      icCorpusAlignedNonVacuousFinalAdequacy icCorpusAlignedBurden :=
  And.intro
    (by
      dsimp only [certifiedFrontierRepresentation_corpus_nems_level2_nv_swap,
        certifiedFrontierRow_corpus_nems_level2_nv, CertifiedFrontierRepresentation.IsPullbackDisplay,
        icCorpusAlignedNonVacuousFinalAdequacy, corpusNemsFin2NvLawfulArchitecture]
      exact corpusNemsFin2NonVacuousFinalAdequacy_pullbackAlong_corpusStrataCarrierSwap.symm)
    (by
      dsimp only [certifiedFrontierRepresentation_corpus_nems_level2_nv_swap,
        certifiedFrontierRow_corpus_nems_level2_nv, CertifiedFrontierRepresentation.IsPullbackDisplay,
        icCorpusAlignedBurden, corpusNemsFin2NvLawfulArchitecture]
      exact corpusNemsFin2Burden_pullbackAlong_corpusStrataCarrierSwap.symm)

theorem absoluteFrontierRawS1_corpus_nems_level2_nv_via_summitRowRepresentation_swap :
    AbsoluteFrontierRawS1 icCorpusAlignedNonVacuousFinalAdequacy icCorpusAlignedBurden :=
  absoluteFrontierRawS1_of_valid_certifiedFrontierRepresentation
    certifiedFrontierRepresentation_corpus_nems_level2_nv_swap
    certifiedFrontierRepresentation_corpus_nems_level2_nv_swap_isPullbackDisplay

/--
**SPEC_035 Program 1 / Q3–S5:** **`pullbackDisplay_with_host_summitFE3`** for **corpus Level-2 NV** with **nontrivial** **`π`**
(**`corpusStrataCarrierSwap`**) — same **host** **`certifiedFrontierRow_corpus_nems_level2_nv`** and **joint** content as the **`id`**
corridor, but **native** display is **not** **`π = id`**. **Parallel** (**S1a** ∧ **host S5-shaped** Stage-C law), **not** collapse of **S5**
to **`U_pullback`** alone.
-/
theorem pullbackDisplay_with_host_summitFE3_corpus_nems_level2_nv_swap :
    (AbsoluteFrontierRawS1 icCorpusAlignedNonVacuousFinalAdequacy icCorpusAlignedBurden) ∧
      (MasterStratifiedAdequacyCascadeAt certifiedFrontierRow_corpus_nems_level2_nv.summitTagged.toHFinal.𝔠
          certifiedFrontierRow_corpus_nems_level2_nv.summitTagged.toHFinal.P
          certifiedFrontierRow_corpus_nems_level2_nv.summitTagged.toHFinal.rcp ∧
        ForgetfulIndexedCoherent certifiedFrontierRow_corpus_nems_level2_nv.fe3.ops ∧
        ForgetfulAgreementInjects certifiedFrontierRow_corpus_nems_level2_nv.fe3.ops) :=
  pullbackDisplay_with_host_summitFE3 certifiedFrontierRepresentation_corpus_nems_level2_nv_swap_isPullbackDisplay

end AdequacyArchitecture.Portability
