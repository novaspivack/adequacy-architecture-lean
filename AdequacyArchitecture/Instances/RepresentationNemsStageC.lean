/-
  **SPEC_032_RQ2 — Stage C (NEMS-first):** honest **parallel composition** of

  1. **Compare-pullback representation** (**`Portability.SummitRowRepresentation`**) — **`AbsoluteFrontierRawS1`**
     on native **`γ`** when **`IsPullbackDisplay`** holds for a **corpus-hosted** certified row, and
  2. **NEMS halting FE-3** forgetful discipline (**`haltingAnchoredNemsIndexedPhantomOps`**) on
     **`HaltingAnchoredFaithfulSummitMasterBundle`**.

  **Non-claim.** There is **no** functorial “pull **`haltingAnchoredNemsBranchGenericCore`** back along **`π : γ → α`**”
  theorem here: NEMS **`Core`** / **`IndexedPhantomCertificateOps`** are **master-bundle** data, while **`π`** in
  **`CertifiedFrontierRepresentation`** compares **Adequacy carriers**. Corpus-facing **`CertifiedFrontierRow`** rows
  still use **`fe3TrivialUnitCore`** in the summit FE-3 slot unless a separate host row closes a different proof
  obligation (**SPEC_032** Stage C program text).

  **Use.** One **conjunctive** cite for artefacts that need **both** the representation-gated **RawS1** corollary and
  the **NEMS** forgetful lemmas — optionally with **Stage B** injective **compare-lift** when
  **`CertifiedFrontierRepresentation.HasInjectiveCompare`**. The host carrier **`α`** is arbitrary (**`Type u`**) —
  **`CorpusStrataCarrier`** is the motivating entry point, not a hypothesis.
-/

import AdequacyArchitecture.Instances.NEMSFe2TheoremFedTransport
import AdequacyArchitecture.Portability.SummitRowRepresentation

namespace AdequacyArchitecture.Instances

universe u

open AdequacyArchitecture
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open AdequacyArchitecture.Portability
open AdequacyArchitecture.Portability.BranchGenericSemanticTransport
open HaltingAnchoredFaithfulSummitMasterBundle
open NemS.Framework
open NemS.MFRR
open NemS.Physical

variable {h : HFinalFrameworkWithNEMAnchoredGlue} {hF : h.F₀ = haltingFramework}

/--
  **Parallel pack (any host `α`).** Representation pullback gate ⇒ **`AbsoluteFrontierRawS1`**; **independently**, NEMS
  halting FE-3 satisfies forgetful coherence and agreement injectivity on **`haltingAnchoredNemsIndexedPhantomOps`**.
-/
theorem repr_pullback_absoluteFrontier_parallel_nems_fe3_forgetful
    {γ α : Type u} {P : AdequacyPredicates γ} {B : BurdenPredicates γ}
    (repr : CertifiedFrontierRepresentation γ α)
    (hdisp : repr.IsPullbackDisplay P B) :
    AbsoluteFrontierRawS1 P B ∧
      ForgetfulIndexedCoherent (@haltingAnchoredNemsIndexedPhantomOps h hF) ∧
      ForgetfulAgreementInjects (@haltingAnchoredNemsIndexedPhantomOps h hF) := by
  refine And.intro ?_ (And.intro ?_ ?_)
  · exact absoluteFrontierRawS1_of_valid_certifiedFrontierRepresentation repr hdisp
  · exact haltingAnchoredNems_forget_coherent
  · exact haltingAnchoredNems_forget_injects

/--
  Same as **`repr_pullback_absoluteFrontier_parallel_nems_fe3_forgetful`**, plus **Stage B** injective **compare-lift**
  along **`repr.π`** from **`HasInjectiveCompare`**.
-/
theorem repr_pullback_pack_absoluteFrontier_nems_fe3_forgetful_injective_compareLift
    {γ α : Type u} {P : AdequacyPredicates γ} {B : BurdenPredicates γ}
    (repr : CertifiedFrontierRepresentation γ α)
    (hdisp : repr.IsPullbackDisplay P B)
    (hπ : repr.HasInjectiveCompare) :
    AbsoluteFrontierRawS1 P B ∧
      ForgetfulIndexedCoherent (@haltingAnchoredNemsIndexedPhantomOps h hF) ∧
      ForgetfulAgreementInjects (@haltingAnchoredNemsIndexedPhantomOps h hF) ∧
      Function.Injective (compareLiftAccountAlong repr.π) := by
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
  · exact absoluteFrontierRawS1_of_valid_certifiedFrontierRepresentation repr hdisp
  · exact haltingAnchoredNems_forget_coherent
  · exact haltingAnchoredNems_forget_injects
  · exact CertifiedFrontierRepresentation.compareLiftAccountAlong_injective_of_repr_injective repr hπ

end AdequacyArchitecture.Instances
