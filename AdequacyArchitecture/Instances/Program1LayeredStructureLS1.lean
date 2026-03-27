/-
  **SPEC_042_LS1 — Layered structure above `U_pullback` (Lean packaging).**

  **Band 2 (S5):** **`pullbackDisplay_with_host_summitFE3`** is **functorial** in the **display** witness: any
  **`Program1AdmissibilityPullbackDisplayWitness`** already packages a **host** **`CertifiedFrontierRow`**, so the
  **second-layer** (**summitFE3** joint **∧** forgetful FE-3 hypotheses) follows **without** new outer input.

  **MU1 corollary:** the same **layer-2** existential packages from **`program1FiniteGAdm`**.
-/

import AdequacyArchitecture.Instances.Program1MetaUnificationMU1
import AdequacyArchitecture.Portability.SummitRowRepresentation

namespace AdequacyArchitecture.Instances

open AdequacyArchitecture.Burden
open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open AdequacyArchitecture.Portability
open AdequacyArchitecture.Portability.BranchGenericSemanticTransport

/--
**LS1-Q4:** **`U_pullback`** **⇒** **∃** display **+** **S5** **parallel** **pack** **(**RawS1 **∧** **host** **joint** **/** **forgetful** **coherence** **)** **on** **the** **same** **witness.**
-/
theorem program1_layer2PullbackDisplay_with_host_summitFE3_of_U_pullback {γ : Type}
    (h : Program1AdmissibilityPullbackDisplayWitness γ) :
    ∃ (α : Type) (repr : CertifiedFrontierRepresentation γ α)
      (P : AdequacyPredicates γ) (B : BurdenPredicates γ),
      repr.IsPullbackDisplay P B ∧
      (AbsoluteFrontierRawS1 P B ∧
        (MasterStratifiedAdequacyCascadeAt repr.certified.summitTagged.toHFinal.𝔠
            repr.certified.summitTagged.toHFinal.P repr.certified.summitTagged.toHFinal.rcp ∧
          ForgetfulIndexedCoherent repr.certified.fe3.ops ∧
          ForgetfulAgreementInjects repr.certified.fe3.ops)) := by
  rcases h with ⟨α, repr, P, B, hd⟩
  exact ⟨α, repr, P, B, hd, pullbackDisplay_with_host_summitFE3 hd⟩

/--
**LS1-Q4** **(**MU1** **hook** **):** **`G_adm`** **⇒** **same** **layer-2** **pack** **(**via** **`U_pullback`**).**
-/
theorem program1_layer2PullbackDisplay_with_host_summitFE3_of_program1FiniteGAdm {γ : Type}
    (h : program1FiniteGAdm γ) :
    ∃ (α : Type) (repr : CertifiedFrontierRepresentation γ α)
      (P : AdequacyPredicates γ) (B : BurdenPredicates γ),
      repr.IsPullbackDisplay P B ∧
      (AbsoluteFrontierRawS1 P B ∧
        (MasterStratifiedAdequacyCascadeAt repr.certified.summitTagged.toHFinal.𝔠
            repr.certified.summitTagged.toHFinal.P repr.certified.summitTagged.toHFinal.rcp ∧
          ForgetfulIndexedCoherent repr.certified.fe3.ops ∧
          ForgetfulAgreementInjects repr.certified.fe3.ops)) :=
  program1_layer2PullbackDisplay_with_host_summitFE3_of_U_pullback
    (program1FiniteGAdm_implies_program1AdmissibilityPullbackDisplayWitness h)

end AdequacyArchitecture.Instances
