/-
  **SPEC_036_FA1 — FA1-NQ12 (`Q₃` / strict intermediate canary):** **parity** quotient of **`Fin 3`**.

  **Neither `Q₁` nor `Q₂`:**
  * **`Q₁`** = **IC** **compare-kernel** quotient toward **`CorpusStrataCarrier`**;
  * **`Q₂`** = **total** equivalence on **`CorpusStrataCarrier`** (**one** host bubble);
  * **`Q₃`** here = **`Fin 3`/parity** — **two** nontrivial classes (**even** **`{0,2}`** vs **odd** **`{1}`**),
    **not** subsingleton, **not** a **kernel-of-compare** on the IC spine.

  **Route A (`G_adm`):** compare-pullback of **`corpusNemsFin2NvLawfulArchitecture`** along **`fin3ParityQuotient_map`**.

  **§8.4:** kernel **`a.val % 2 = b.val % 2`** on **`Fin 3`** — strict **intermediate** coarsening.
-/

import AdequacyArchitecture.Instances.NEMSBridgeCoreRecord
import AdequacyArchitecture.Lawful.ComparePullback
import AdequacyArchitecture.Lawful.FinalConditionalSummit
import AdequacyArchitecture.Lawful.LawfulStructures
import AdequacyArchitecture.Portability.CertifiedFrontierRow
import AdequacyArchitecture.Portability.SummitRowRepresentation

namespace AdequacyArchitecture.Instances

open AdequacyArchitecture
open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open AdequacyArchitecture.Portability
open AdequacyArchitecture.Portability.BranchGenericSemanticTransport

/-- **Parity** kernel on **`Fin 3`**. -/
def fin3ParityKernel (a b : Fin 3) : Prop :=
  a.val % 2 = b.val % 2

/-- **Advisor `Q₃`:** **2** classes, **3** preimages (**merge** **`0`** and **`2`**). -/
def fin3ParityQuotient : Type :=
  Quot fin3ParityKernel

private def fin3ParityRepresentativeMap (i : Fin 3) : CorpusStrataCarrier :=
  ⟨i.val % 2, Nat.mod_lt i.val (Nat.zero_lt_succ 1)⟩

private theorem fin3ParityRepresentativeMap_respects (a b : Fin 3) (h : fin3ParityKernel a b) :
    fin3ParityRepresentativeMap a = fin3ParityRepresentativeMap b := by
  apply Fin.ext
  simpa [fin3ParityRepresentativeMap, h]

def fin3ParityQuotient_map : fin3ParityQuotient → CorpusStrataCarrier :=
  Quot.lift fin3ParityRepresentativeMap fin3ParityRepresentativeMap_respects

def fin3ParityQuotient_pullbackLawful : LawfulAdequacyArchitecture fin3ParityQuotient :=
  lawfulAdequacyArchitecture_pullbackAlongCompare fin3ParityQuotient_map
    corpusNemsFin2NvLawfulArchitecture

theorem fin3ParityQuotient_pullback_absoluteFrontierRawS1 :
    AbsoluteFrontierRawS1 fin3ParityQuotient_pullbackLawful.P fin3ParityQuotient_pullbackLawful.B :=
  universal_irreducible_adequacy_lawful fin3ParityQuotient_pullbackLawful

def fin3ParityQuotientRepr :
    CertifiedFrontierRepresentation fin3ParityQuotient CorpusStrataCarrier where
  π := fin3ParityQuotient_map
  certified := certifiedFrontierRow_corpus_nems_level2_nv

theorem fin3ParityQuotientRepr_isPullbackDisplay :
    fin3ParityQuotientRepr.IsPullbackDisplay
      fin3ParityQuotient_pullbackLawful.P
      fin3ParityQuotient_pullbackLawful.B :=
  And.intro rfl rfl

theorem fin3ParityQuotientRepr_hasInjectiveCompare :
    fin3ParityQuotientRepr.HasInjectiveCompare := by
  intro x y hπ
  induction x using Quot.induction_on with
  | h a =>
    induction y using Quot.induction_on with
    | h b =>
      refine Quot.sound ?_
      have hval : (fin3ParityRepresentativeMap a).val = (fin3ParityRepresentativeMap b).val :=
        congrArg Fin.val hπ
      simpa [fin3ParityKernel, fin3ParityRepresentativeMap] using hval

theorem fin3ParityQuotient_pullbackDisplay_with_host_summitFE3 :
    (AbsoluteFrontierRawS1 fin3ParityQuotient_pullbackLawful.P
        fin3ParityQuotient_pullbackLawful.B) ∧
      (MasterStratifiedAdequacyCascadeAt certifiedFrontierRow_corpus_nems_level2_nv.summitTagged.toHFinal.𝔠
          certifiedFrontierRow_corpus_nems_level2_nv.summitTagged.toHFinal.P
          certifiedFrontierRow_corpus_nems_level2_nv.summitTagged.toHFinal.rcp ∧
        ForgetfulIndexedCoherent certifiedFrontierRow_corpus_nems_level2_nv.fe3.ops ∧
        ForgetfulAgreementInjects certifiedFrontierRow_corpus_nems_level2_nv.fe3.ops) :=
  pullbackDisplay_with_host_summitFE3 fin3ParityQuotientRepr_isPullbackDisplay

theorem fin3ParityQuotient_mk_zero_ne_mk_one :
    Quot.mk fin3ParityKernel (⟨0, by decide⟩ : Fin 3) ≠
      Quot.mk fin3ParityKernel ⟨1, by decide⟩ := by
  intro he
  have hπ := congrArg fin3ParityQuotient_map he
  simp [fin3ParityQuotient_map, fin3ParityRepresentativeMap] at hπ

end AdequacyArchitecture.Instances
