/-
  **SPEC_033_RL9 — representation-calculus v2 / branch-role gate (Phases A–D).**

  **Phase A.** **`CertifiedSummitRowRepresentation`** ties **`SummitRowRepresentation`** to a **Stage G**
  **`CertifiedUpgradeWitness`** on the host, aligning **`repr.certified`** with **`hostUpgrade.toCertifiedFrontierRow`**.

  **Phase B.** From **pullback display** on **`γ`**, package **target `AbsoluteFrontierRawS1`** together with host **Layer A**
  cascade + **FE-3 forgetful joint law** on the **certified** row (**no** new τ- or tag-axioms).

  **Phase C.** **`branchRole`** coherence between **`repr.certified`** and **`hostUpgrade`**, plus wiring a
  **`RoleAwareThreeBranchFrontierPackage`** when the host row shares **`HFinal`** with the standard corpus package.

  **Phase D.** **Sharpness:** host **`Nonempty (HFinal α)`** from the gate; **display** remains the honest **RawS1** gate on **`γ`**;
  global **counterexample** names (**Stage H**) cited for **∀P,B** impossibility.

  **Note (Stage G phrasing):** when **`certified_matches_host`**, **`summitFE3_joint_semantic_law_of_certifiedUpgradeWitness gate.hostUpgrade`**
  and **`certifiedFrontierRow_summitFE3_joint gate.repr.certified`** are the **same** proposition — rewrite along
  **`congrArg certifiedFrontierRow_summitFE3_joint`** (or unfold **`summitFE3_joint_semantic_law_of_certifiedUpgradeWitness`**).
-/

import AdequacyArchitecture.Instances.ICCompareRepresentationPullback
import AdequacyArchitecture.Instances.RoleAwareThreeBranchFrontier
import AdequacyArchitecture.Lawful.FinalConditionalSummit
import AdequacyArchitecture.Lawful.RidgeSummitStatements
import AdequacyArchitecture.Portability.CertifiedFrontierRow
import AdequacyArchitecture.Portability.RepresentationCalculusMX7
import AdequacyArchitecture.Portability.S1ShapeNecessityCounterexample
import AdequacyArchitecture.Portability.SummitRowRepresentation

universe u

namespace AdequacyArchitecture.Portability

open AdequacyArchitecture.Instances
open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open AdequacyArchitecture.Portability.BranchGenericSemanticTransport
open AdequacyArchitecture.Summit

variable {γ α : Type u}

/-! ## Phase A — interface -/

/--
**SPEC_033 Phase A — certified summit-row + upgrade witness alignment.**

* **`repr`:** compare-pullback **summit row representation** (**SPEC_032**).
* **`hostUpgrade`:** **Stage G** certified-upgrade witness on the host (**SPEC_030 / `RepresentationCalculusMX7`**).
* **`certified_matches_host`:** the represented **certified row** is **exactly** the row assembled from the upgrade
  (the honest **non-smuggling** link between **RQ2** and **MX7** vocabularies).
-/
structure CertifiedSummitRowRepresentation (γ α : Type u) where
  repr : CertifiedFrontierRepresentation γ α
  hostUpgrade : CertifiedUpgradeWitness α
  certified_matches_host : repr.certified = hostUpgrade.toCertifiedFrontierRow

/-- **Canonical gate:** every **`CertifiedFrontierRepresentation`** lifts via **`certifiedUpgradeWitness_of_certifiedFrontierRow`**. -/
def CertifiedSummitRowRepresentation.canonical (repr : CertifiedFrontierRepresentation γ α) :
    CertifiedSummitRowRepresentation γ α where
  repr := repr
  hostUpgrade := certifiedUpgradeWitness_of_certifiedFrontierRow repr.certified
  certified_matches_host := rfl

/-- Optional **injective compare** on the **`repr`** spine (same predicate as **SPEC_032 Stage B**). -/
abbrev CertifiedSummitRowRepresentation.HasInjectiveCompare (gate : CertifiedSummitRowRepresentation γ α) : Prop :=
  gate.repr.HasInjectiveCompare

/-- Pullback display predicate — **SPEC_032** alignment on **`γ`**. -/
abbrev CertifiedSummitRowRepresentation.IsPullbackDisplay (gate : CertifiedSummitRowRepresentation γ α)
    (P : AdequacyPredicates γ) (B : BurdenPredicates γ) : Prop :=
  gate.repr.IsPullbackDisplay P B

/-! ### Citation aliases (**SPEC_033 v2**) — stable **`Prop`** surface for FE-3 joint law

**Naming:** avoid the prefix **`CertifiedFrontierRow…`** on a **`def`** — it can elaborate as a **structure namespace**
path and break **`Prop`** typing in this module.
-/

/--
**SPEC_030 Stage C — packaged row joint** (Layer A cascade + FE-3 forgetful discipline) under one **`Prop`** name
for cites (**avoids** long **`∧`** chains in informal text).

**Note:** do **not** bind this to **`certifiedFrontierRow_summitFE3_joint row`** — that application is a **proof term**; here we
need the **proposition** spelled as a type of sort **`Prop`**.
-/
def SummitFE3JointPackOfCertifiedRow {β : Type u} (row : CertifiedFrontierRow β) : Prop :=
  MasterStratifiedAdequacyCascadeAt row.summitTagged.toHFinal.𝔠 row.summitTagged.toHFinal.P row.summitTagged.toHFinal.rcp ∧
    ForgetfulIndexedCoherent row.fe3.ops ∧ ForgetfulAgreementInjects row.fe3.ops

/--
**SPEC_030 Stage G (`RepresentationCalculusMX7`) — upgrade phrasing** of the **same** joint (**defeq** to the **statement** of
**`summitFE3_joint_semantic_law_of_certifiedUpgradeWitness`**, since **`toSummitFE3`** is **`⟨summitTagged, fe3⟩`**).
-/
abbrev SummitFE3JointPackOfUpgradeWitness {β : Type u} (w : CertifiedUpgradeWitness β) : Prop :=
  SummitFE3JointPackOfCertifiedRow w.toCertifiedFrontierRow

/--
**Gate coherence:** after **`certified_matches_host`**, the **MX7** name and the **row** name denote the **same** joint fact.
-/
theorem certifiedSummitRowRepr_summitFE3_joint_upgrade_iff_row (gate : CertifiedSummitRowRepresentation γ α) :
    SummitFE3JointPackOfUpgradeWitness gate.hostUpgrade ↔ SummitFE3JointPackOfCertifiedRow gate.repr.certified :=
  Iff.of_eq (congrArg SummitFE3JointPackOfCertifiedRow gate.certified_matches_host.symm)

/-! ## Phase B — pullback target consequences + host summit spine -/

theorem absoluteFrontierRawS1_of_isPullbackDisplay (gate : CertifiedSummitRowRepresentation γ α)
    {P : AdequacyPredicates γ} {B : BurdenPredicates γ}
    (h : CertifiedSummitRowRepresentation.IsPullbackDisplay gate P B) :
    AbsoluteFrontierRawS1 P B :=
  absoluteFrontierRawS1_of_valid_certifiedFrontierRepresentation gate.repr h

theorem masterStratifiedAdequacyCascadeAt_host_certified (gate : CertifiedSummitRowRepresentation γ α) :
    MasterStratifiedAdequacyCascadeAt gate.repr.certified.summitTagged.toHFinal.𝔠
      gate.repr.certified.summitTagged.toHFinal.P gate.repr.certified.summitTagged.toHFinal.rcp :=
  highestReachable_summit_at gate.repr.certified.summitTagged.toHFinal

theorem certifiedFrontierRow_summitFE3_joint_on_host (gate : CertifiedSummitRowRepresentation γ α) :
    MasterStratifiedAdequacyCascadeAt gate.repr.certified.summitTagged.toHFinal.𝔠
        gate.repr.certified.summitTagged.toHFinal.P gate.repr.certified.summitTagged.toHFinal.rcp ∧
      ForgetfulIndexedCoherent gate.repr.certified.fe3.ops ∧
        ForgetfulAgreementInjects gate.repr.certified.fe3.ops :=
  certifiedFrontierRow_summitFE3_joint gate.repr.certified

/--
**SPEC_033 Phase B (master pack):** pullback display on **`γ`** ⇒ **target RawS1** **and** the full **host** summit + **FE-3** joint spine
carried by the **certified** host row (.specialize via **`gate.certified_matches_host`** to **`hostUpgrade`** lemmas).
-/
theorem pullback_display_consequences_pack (gate : CertifiedSummitRowRepresentation γ α)
    {P : AdequacyPredicates γ} {B : BurdenPredicates γ}
    (h : CertifiedSummitRowRepresentation.IsPullbackDisplay gate P B) :
    AbsoluteFrontierRawS1 P B ∧
      MasterStratifiedAdequacyCascadeAt gate.repr.certified.summitTagged.toHFinal.𝔠
        gate.repr.certified.summitTagged.toHFinal.P gate.repr.certified.summitTagged.toHFinal.rcp ∧
      ForgetfulIndexedCoherent gate.repr.certified.fe3.ops ∧
        ForgetfulAgreementInjects gate.repr.certified.fe3.ops :=
  ⟨absoluteFrontierRawS1_of_isPullbackDisplay gate h, certifiedFrontierRow_summitFE3_joint_on_host gate⟩

/-! ## Phase C — branch-role + standard role-aware package -/

theorem branchRole_eq_hostUpgrade (gate : CertifiedSummitRowRepresentation γ α) :
    gate.repr.certified.summitTagged.branchRole = gate.hostUpgrade.branchRole := by
  have hσ := congrArg CertifiedFrontierRow.summitTagged gate.certified_matches_host
  exact congrArg HFinalWithBranchRole.branchRole hσ

/--
**FACTORIZATION (corpus host):** if the certified host row shares **`HFinal`** with the **NEMS relocation** leg of a
**`RoleAwareThreeBranchFrontierPackage`**, then the **Layer A** master cascade for that row is exactly the package's
**relocation** cascade — **branch-role tag** may still differ on the **IC** leg (**same `HFinal`, different `branchRole` views**).
-/
theorem masterStratifiedAdequacyCascadeAt_of_roleAware_pkg_sameHFinal
    (pkg : RoleAwareThreeBranchFrontierPackage) (row : CertifiedFrontierRow CorpusStrataCarrier)
    (hHF : pkg.nemsRelocationTagged.toHFinal = row.summitTagged.toHFinal) :
    MasterStratifiedAdequacyCascadeAt row.summitTagged.toHFinal.𝔠 row.summitTagged.toHFinal.P
        row.summitTagged.toHFinal.rcp := by
  rw [← congrArg HFinal.𝔠 hHF, ← congrArg HFinal.P hHF, ← congrArg HFinal.rcp hHF]
  exact roleAwareFrontierPackage_corpus_relocation_master_cascade pkg

/-! ### **IC CS-3** compare pullback (**SPEC_031 / SPEC_032**) — nontrivial **`π`** (**SPEC_033 v2**) -/

/--
**Native IC spine compression carrier** represents into the **same** corpus **Level 2 NV** certified row as
**`icCs3CertifiedFrontierRepresentation`**, canonically upgraded to a **`CertifiedUpgradeWitness`** on the host.
-/
def icCs3_pullback_certifiedSummitRowRepr : CertifiedSummitRowRepresentation icNemsSpineCompressionCarrier CorpusStrataCarrier :=
  CertifiedSummitRowRepresentation.canonical icCs3CertifiedFrontierRepresentation

theorem icCs3_pullback_certifiedSummitRowRepr_isPullbackDisplay :
    CertifiedSummitRowRepresentation.IsPullbackDisplay icCs3_pullback_certifiedSummitRowRepr
      icNativeCompressionLawfulArchitecture_cs3_pullback.P
      icNativeCompressionLawfulArchitecture_cs3_pullback.B :=
  icCs3CertifiedFrontierRepresentation_isPullbackDisplay

/--
**SPEC_033 v2 master pack** on the **IC CS-3** row: target **RawS1** on the compression carrier + **host** summit / FE-3 joint
(carrier-agnostic **Unit** FE-3 core — **no** native **IndexedPhantomCertificateOps** along **`compareToCorpus`** per **SPEC_031 Stage B**).
-/
theorem icCs3_pullback_certifiedSummitRowRepr_pullback_pack :
    AbsoluteFrontierRawS1 icNativeCompressionLawfulArchitecture_cs3_pullback.P
      icNativeCompressionLawfulArchitecture_cs3_pullback.B ∧
      MasterStratifiedAdequacyCascadeAt certifiedFrontierRow_corpus_nems_level2_nv.summitTagged.toHFinal.𝔠
        certifiedFrontierRow_corpus_nems_level2_nv.summitTagged.toHFinal.P
        certifiedFrontierRow_corpus_nems_level2_nv.summitTagged.toHFinal.rcp ∧
      ForgetfulIndexedCoherent certifiedFrontierRow_corpus_nems_level2_nv.fe3.ops ∧
        ForgetfulAgreementInjects certifiedFrontierRow_corpus_nems_level2_nv.fe3.ops :=
  pullback_display_consequences_pack icCs3_pullback_certifiedSummitRowRepr
    icCs3_pullback_certifiedSummitRowRepr_isPullbackDisplay

theorem icCs3_pullback_certifiedSummitRowRepr_summitFE3_joint_ui :
    SummitFE3JointPackOfCertifiedRow icCs3_pullback_certifiedSummitRowRepr.repr.certified ↔
      SummitFE3JointPackOfUpgradeWitness icCs3_pullback_certifiedSummitRowRepr.hostUpgrade :=
  (certifiedSummitRowRepr_summitFE3_joint_upgrade_iff_row icCs3_pullback_certifiedSummitRowRepr).symm

/-! ### Standard corpus **Level 2 NV / IC CS-3 aligned** identity gate -/

def corpusNemsLevel2Nv_id : CertifiedSummitRowRepresentation CorpusStrataCarrier CorpusStrataCarrier :=
  CertifiedSummitRowRepresentation.canonical certifiedFrontierRepresentation_corpus_nems_level2_nv_id

theorem corpusNemsLevel2Nv_id_isPullbackDisplay :
    CertifiedSummitRowRepresentation.IsPullbackDisplay corpusNemsLevel2Nv_id
      icCorpusAlignedNonVacuousFinalAdequacy icCorpusAlignedBurden :=
  certifiedFrontierRepresentation_corpus_nems_level2_nv_id_isPullbackDisplay

theorem corpusNemsLevel2Nv_id_pullback_pack :
    AbsoluteFrontierRawS1 icCorpusAlignedNonVacuousFinalAdequacy icCorpusAlignedBurden ∧
      MasterStratifiedAdequacyCascadeAt certifiedFrontierRow_corpus_nems_level2_nv.summitTagged.toHFinal.𝔠
        certifiedFrontierRow_corpus_nems_level2_nv.summitTagged.toHFinal.P
        certifiedFrontierRow_corpus_nems_level2_nv.summitTagged.toHFinal.rcp ∧
      ForgetfulIndexedCoherent certifiedFrontierRow_corpus_nems_level2_nv.fe3.ops ∧
        ForgetfulAgreementInjects certifiedFrontierRow_corpus_nems_level2_nv.fe3.ops :=
  pullback_display_consequences_pack corpusNemsLevel2Nv_id corpusNemsLevel2Nv_id_isPullbackDisplay

theorem standardRoleAware_pkg_nemsRelocation_sameHFinal_corpusNv_row :
    standardRoleAwareThreeBranchFrontierPackage.nemsRelocationTagged.toHFinal =
      certifiedFrontierRow_corpus_nems_level2_nv.summitTagged.toHFinal :=
  rfl

theorem corpusNemsLevel2Nv_id_master_cascade_via_standardRoleAwarePackage :
    MasterStratifiedAdequacyCascadeAt certifiedFrontierRow_corpus_nems_level2_nv.summitTagged.toHFinal.𝔠
      certifiedFrontierRow_corpus_nems_level2_nv.summitTagged.toHFinal.P
      certifiedFrontierRow_corpus_nems_level2_nv.summitTagged.toHFinal.rcp :=
  masterStratifiedAdequacyCascadeAt_of_roleAware_pkg_sameHFinal standardRoleAwareThreeBranchFrontierPackage
    certifiedFrontierRow_corpus_nems_level2_nv standardRoleAware_pkg_nemsRelocation_sameHFinal_corpusNv_row

/-! ## Phase D — sharpness / honest ceilings -/

theorem nonempty_hfinal_host (gate : CertifiedSummitRowRepresentation γ α) : Nonempty (HFinal α) :=
  nonempty_certifiedFrontierRow_implies_nonempty_hfinal ⟨gate.repr.certified⟩

theorem not_nonempty_certifiedSummitRowRepr_of_not_nonempty_hfinal_host (h : ¬ Nonempty (HFinal α)) :
    ¬ Nonempty (CertifiedSummitRowRepresentation γ α) := by
  rintro ⟨⟨_, w, _⟩⟩
  exact h (nonempty_certifiedFrontierRow_implies_nonempty_hfinal ⟨w.toCertifiedFrontierRow⟩)

/--
**Bridge to Stage H global obstruction:** the **same** **`AbsoluteFrontierRawS1`** name is **false** on an explicit pair
on **any** carrier — see **`stageH_not_absoluteFrontierRawS1_on_counterexamplePair`**.
There is **no** proof of **`∀ P B, AbsoluteFrontierRawS1 P B`** at this layer without **smuggling** or **false** axioms.
-/
theorem absoluteFrontierRawS1_global_counterexample_pointer (β : Type u) :
    ¬ AbsoluteFrontierRawS1 (s1CounterexampleReprOnlyAdequacy β) (s1CounterexampleEmptyBurden β) :=
  not_absoluteFrontierRawS1Counterexample (α := β)

end AdequacyArchitecture.Portability
