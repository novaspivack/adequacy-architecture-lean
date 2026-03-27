/-
  **SPEC_037_MU1 — Phase M (Lean core).**

  **Meta-unification fact:** **`program1FiniteGAdm γ` ↔ `Program1AdmissibilityPullbackDisplayWitness γ`**.

  * **`pullback`** constructor — identity.
  * **`upgradeWitness`** — **`CertifiedUpgradeWitness.toCertifiedFrontierRow`** with **identity** compare **`π = id`**
    and **`pullbackAlongCompare_id`** (**`Lawful/ComparePullback`**).
  * **`icStageDFullPack`** — **`γ = icNemsSpineCompressionCarrier`**; witness from global
    **`program1_program1AdmissibilityPullbackDisplayWitness_icCs3SpineCompression`**
    (**IC pack fields unused** for this implication — documented in **SPEC_037** memos).

  **Consequence:** **`U_pullback`** (**S1a / Program 1**) is the **unique** **outer** **Prop** **gate** **up** **to**
  **logical** **equivalence** **with** **`G_adm`** **as** **currently** **defined** — **not** **a** **new** **definition**,
  **but** **a** **proved** **collapse** **of** **the** **three** **witness** **routes**.

  **SPEC_039_MX1 (maximality fragment):** **`Nonempty (CertifiedFrontierRow γ) ⇒ U_pullback`** —
  **`program1AdmissibilityPullbackDisplayWitness_of_nonempty_certifiedFrontierRow`**.
-/

import AdequacyArchitecture.Instances.ProgramFiniteAdmissibility
import AdequacyArchitecture.Lawful.ComparePullback
import AdequacyArchitecture.Portability.CertifiedFrontierRow
import AdequacyArchitecture.Portability.RepresentationCalculusMX7
import AdequacyArchitecture.Portability.SummitRowRepresentation

namespace AdequacyArchitecture.Instances

open AdequacyArchitecture.AbsoluteFrontier
open AdequacyArchitecture.Burden
open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open AdequacyArchitecture.Portability

variable {γ : Type}

/-- **Identity-compare** representation of a **`CertifiedFrontierRow`** (host = native carrier). -/
def certifiedFrontierRow_idCertifiedFrontierRepresentation (row : CertifiedFrontierRow γ) :
    CertifiedFrontierRepresentation γ γ where
  π := id
  certified := row

theorem certifiedFrontierRow_idCertifiedFrontierRepresentation_isPullbackDisplay (row : CertifiedFrontierRow γ) :
    (certifiedFrontierRow_idCertifiedFrontierRepresentation row).IsPullbackDisplay row.lawful.P row.lawful.B := by
  simp only [CertifiedFrontierRepresentation.IsPullbackDisplay, certifiedFrontierRow_idCertifiedFrontierRepresentation]
  refine And.intro ?_ ?_
  · exact (AdequacyPredicates.pullbackAlongCompare_id row.lawful.P).symm
  · exact (BurdenPredicates.pullbackAlongCompare_id row.lawful.B).symm

theorem program1AdmissibilityPullbackDisplayWitness_of_certifiedFrontierRow (row : CertifiedFrontierRow γ) :
    Program1AdmissibilityPullbackDisplayWitness γ :=
  ⟨γ, certifiedFrontierRow_idCertifiedFrontierRepresentation row, row.lawful.P, row.lawful.B,
    certifiedFrontierRow_idCertifiedFrontierRepresentation_isPullbackDisplay row⟩

theorem program1AdmissibilityPullbackDisplayWitness_of_nonempty_certifiedFrontierRow
    (h : Nonempty (CertifiedFrontierRow γ)) : Program1AdmissibilityPullbackDisplayWitness γ := by
  rcases h with ⟨row⟩
  exact program1AdmissibilityPullbackDisplayWitness_of_certifiedFrontierRow row

theorem program1AdmissibilityPullbackDisplayWitness_of_certifiedUpgradeWitness (w : CertifiedUpgradeWitness γ) :
    Program1AdmissibilityPullbackDisplayWitness γ :=
  program1AdmissibilityPullbackDisplayWitness_of_certifiedFrontierRow w.toCertifiedFrontierRow

theorem program1AdmissibilityPullbackDisplayWitness_of_program1FiniteGAdmWitness (w : Program1FiniteGAdm γ) :
    Program1AdmissibilityPullbackDisplayWitness γ :=
  match w with
  | Program1FiniteGAdm.pullback h => h
  | Program1FiniteGAdm.icStageDFullPack he _ => by
      subst he
      exact program1_program1AdmissibilityPullbackDisplayWitness_icCs3SpineCompression
  | Program1FiniteGAdm.upgradeWitness w' =>
      program1AdmissibilityPullbackDisplayWitness_of_certifiedUpgradeWitness w'

theorem program1FiniteGAdm_implies_program1AdmissibilityPullbackDisplayWitness (h : program1FiniteGAdm γ) :
    Program1AdmissibilityPullbackDisplayWitness γ := by
  rcases h with ⟨w⟩
  exact program1AdmissibilityPullbackDisplayWitness_of_program1FiniteGAdmWitness w

theorem program1AdmissibilityPullbackDisplayWitness_implies_program1FiniteGAdm
    (h : Program1AdmissibilityPullbackDisplayWitness γ) : program1FiniteGAdm γ :=
  Nonempty.intro (Program1FiniteGAdm.pullback h)

theorem program1FiniteGAdm_iff_program1AdmissibilityPullbackDisplayWitness {γ : Type} :
    program1FiniteGAdm γ ↔ Program1AdmissibilityPullbackDisplayWitness γ :=
  Iff.intro program1FiniteGAdm_implies_program1AdmissibilityPullbackDisplayWitness
    program1AdmissibilityPullbackDisplayWitness_implies_program1FiniteGAdm

/--
**MU1-Q6 / flagship chain:** factor **`G_adm` → `U_pullback` → RawS1** (**second** **step** **is**
**`exists_absoluteFrontierRawS1_of_program1Admissibility_pullbackDisplayWitness`**).
-/
theorem program1FiniteGAdm_implies_exists_absoluteFrontierRawS1_via_U_pullback {γ : Type} (h : program1FiniteGAdm γ) :
    ∃ (P : AdequacyPredicates γ) (B : BurdenPredicates γ), AbsoluteFrontierRawS1 P B :=
  exists_absoluteFrontierRawS1_of_program1Admissibility_pullbackDisplayWitness
    (program1FiniteGAdm_implies_program1AdmissibilityPullbackDisplayWitness h)

end AdequacyArchitecture.Instances
