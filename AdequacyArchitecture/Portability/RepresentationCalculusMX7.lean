/-
  **SPEC_030_MX7 — Stages G & H (v1)** — **representation calculus** + **honest absolute-frontier crown** scaffolding.

  **Stage G (representation / instantiation rules).** Packages the minimal **theorem schema** “external domain
  supplies **`SummitContractBase`** + aligned **`HFinalWithBranchRole`** + **FE-3** slot ⇒ **`CertifiedFrontierRow`**”,
  and records the **sharp certified ⇒ `HFinal`** obstruction. (**SPEC_028** Stage I **`SummitContractBase`** is the
  𝒞-only entry; this is the **upgrade** to the SPEC_030 over-class row.)

  **Stage H (crown).** The **proved** gates are **split** (no smuggling):
  * **`CertifiedFrontierRow`** ⇒ **`AbsoluteFrontierRawS1`** for the lawful pair (**already** Stage A);
  * **`HFrontier`** ⇒ **Layer A** master cascade (**SPEC_027** apex);
  * **unrestricted** Layer-B **`AbsoluteFrontierRawS1 ∀ P,B`** is **refuted** by the Stage B+ counterexample pair on
    **any** carrier.

  **Note:** Bool v2 / raw **`∀P,B`** global theorems remain **out of scope** (see SPEC_030 Stage A table).
-/

import AdequacyArchitecture.AbsoluteFrontier.AF5_Apex
import AdequacyArchitecture.Lawful.FinalConditionalSummit
import AdequacyArchitecture.Portability.BranchGenericSemanticTransport
import AdequacyArchitecture.Portability.CertifiedFrontierRow
import AdequacyArchitecture.Portability.GenericSemanticSummitLift
import AdequacyArchitecture.Portability.InstantiationCalculus
import AdequacyArchitecture.Portability.S1ShapeNecessityCounterexample
import AdequacyArchitecture.Summit.UniversalIrreducibleAdequacy

universe u

namespace AdequacyArchitecture.Portability

open AdequacyArchitecture.AbsoluteFrontier
open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open AdequacyArchitecture.Portability.BranchGenericSemanticTransport
open AdequacyArchitecture.Summit

variable {α : Type u}

/-! ## Stage G — external 𝒞 base + summit / FE-3 supplement -/

/--
**SPEC_030 Stage G — certified upgrade witness** (domain-neutral type).

An external domain that has proved **`SummitContractBase`** (𝒞) **and** supplies an **`HFinal`**-shaped summit tag with
**`P` alignment** and an **FE-3** core can form a **`CertifiedFrontierRow`** without new axioms.
-/
structure CertifiedUpgradeWitness (α : Type u) where
  base : SummitContractBase α
  summitTagged : HFinalWithBranchRole α
  summit_lawful_sameAdequacy : summitTagged.toHFinal.P = base.arch.P
  fe3 : Fe3UnitCore

/-- Assemble the SPEC_030 **certified frontier row** from a **certified upgrade** witness. -/
def CertifiedUpgradeWitness.toCertifiedFrontierRow (w : CertifiedUpgradeWitness α) : CertifiedFrontierRow α :=
  ⟨w.base.arch, w.summitTagged, w.summit_lawful_sameAdequacy, w.fe3⟩

/--
**SPEC_030 / SPEC_033 — canonical reverse:** every **`CertifiedFrontierRow`** is definitionally the **Stage G upgrade**
packaging of its **`𝒞` + summit + FE-3** fields (**`SummitContractBase.ofLawful row.lawful`**).
-/
def certifiedUpgradeWitness_of_certifiedFrontierRow (row : CertifiedFrontierRow α) : CertifiedUpgradeWitness α where
  base := SummitContractBase.ofLawful row.lawful
  summitTagged := row.summitTagged
  summit_lawful_sameAdequacy := row.summit_lawful_sameAdequacy
  fe3 := row.fe3

@[simp]
theorem certifiedUpgradeWitness_of_certifiedFrontierRow_toCertifiedFrontierRow (row : CertifiedFrontierRow α) :
    (certifiedUpgradeWitness_of_certifiedFrontierRow row).toCertifiedFrontierRow = row :=
  rfl

/-- **Layer B (∂ RawS1):** certified upgrade ⇒ **`AbsoluteFrontierRawS1`** for **`base.arch`**. -/
theorem absoluteFrontierRawS1_of_certifiedUpgradeWitness (w : CertifiedUpgradeWitness α) :
    AbsoluteFrontierRawS1 w.base.arch.P w.base.arch.B :=
  absoluteFrontierRawS1_of_certifiedFrontierRow w.toCertifiedFrontierRow

/-- **Stage C joint law** on the packaged row (**FE-3** + summit fields; proposition spelt out). -/
theorem summitFE3_joint_semantic_law_of_certifiedUpgradeWitness (w : CertifiedUpgradeWitness α) :
    MasterStratifiedAdequacyCascadeAt w.toCertifiedFrontierRow.toSummitFE3.summitTagged.toHFinal.𝔠
      w.toCertifiedFrontierRow.toSummitFE3.summitTagged.toHFinal.P
      w.toCertifiedFrontierRow.toSummitFE3.summitTagged.toHFinal.rcp ∧
      ForgetfulIndexedCoherent w.toCertifiedFrontierRow.toSummitFE3.fe3.ops ∧
        ForgetfulAgreementInjects w.toCertifiedFrontierRow.toSummitFE3.fe3.ops :=
  certifiedFrontierRow_summitFE3_joint w.toCertifiedFrontierRow

/-- Read-off of the **SPEC_026/030 branch role** tag from the supplement. -/
def CertifiedUpgradeWitness.branchRole (w : CertifiedUpgradeWitness α) : SummitBranchRole :=
  w.summitTagged.branchRole

/-! ## Stage G — obstruction (certified row needs `HFinal`) -/

theorem not_nonempty_certifiedFrontierRow_of_not_nonempty_hfinal {β : Type u}
    (h : ¬ Nonempty (HFinal β)) : ¬ Nonempty (CertifiedFrontierRow β) := by
  rintro hn
  exact h (nonempty_certifiedFrontierRow_implies_nonempty_hfinal hn)

/-! ## Stage H — honest crown (split gates; sharp global obstruction) -/

/--
**SPEC_030 Stage H (v1) — 𝒞 + certified packaging ⇒ Layer-B name** (same proof spine as Stage A).
-/
theorem stageH_certifiedFrontierRow_implies_absoluteFrontierRawS1 (row : CertifiedFrontierRow α) :
    AbsoluteFrontierRawS1 row.lawful.P row.lawful.B :=
  absoluteFrontierRawS1_of_certifiedFrontierRow row

/--
**SPEC_027 apex gate — `HFrontier` ⇒ Layer A master cascade** (re-export shape; cite **`apex_master_cascade_from_hFrontier`**).
-/
theorem stageH_hFrontier_implies_masterStratifiedCascade {β : Type u} (H : HFrontier β) :
    MasterStratifiedAdequacyCascadeAt H.hf.𝔠 H.hf.P H.hf.rcp :=
  apex_master_cascade_from_hFrontier H

/--
**SPEC_030 Stage H — sharp obstruction:** the **same** **`AbsoluteFrontierRawS1`** **name** is **false** for a fully
explicit **`P,B`** on **any** carrier — so there is **no** honest **unparameterized** `∀ P B, …` theorem at this layer.
-/
theorem stageH_not_absoluteFrontierRawS1_on_counterexamplePair :
    ¬ AbsoluteFrontierRawS1 (s1CounterexampleReprOnlyAdequacy α) (s1CounterexampleEmptyBurden α) :=
  not_absoluteFrontierRawS1Counterexample

/-- **Parsable marker:** SPEC_027 apex posture (**`provedOverClass`**) at the time of SPEC_030 G/H v1 closure. -/
theorem stageH_apex_kind_eq_postSPEC027 : apexPostSPEC027 = AbsoluteFrontierApexKind.provedOverClass :=
  rfl

end AdequacyArchitecture.Portability
