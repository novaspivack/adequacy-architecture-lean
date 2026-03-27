/-
  **SPEC_041_OG1 — Outer gate grammar / grammar-cut Max-A.**

  **Minimal** `Program1OuterGateGrammar` captures the theorem-relevant fragment of MA1 normal forms **NF0–NF3**
  (pullback display, finite `G_adm`, nonempty certified row, nonempty upgrade witness). **NF4** (pure `S1Lawful`
  only) is **deliberately excluded** — the hazard identified in SPEC_040_MA1.

  **Max-A (grammar-cut):** every grammar interpretation **`g.interp γ`** implies **`program1FiniteGAdm γ`**, hence
  **`Program1AdmissibilityPullbackDisplayWitness γ`** (MU1). Any **`C : Type → Prop`** **grammar-generated**
  (**∃** `g`, **`C γ ↔ g.interp γ`**) inherits **`C ⊆ U_pullback`** and **`Sound C`**.
-/

import AdequacyArchitecture.Instances.ProgramFiniteAdmissibility
import AdequacyArchitecture.Instances.Program1MetaUnificationMU1
import AdequacyArchitecture.Instances.Program1MaximalityMA1
import AdequacyArchitecture.Portability.RepresentationCalculusMX7

namespace AdequacyArchitecture.Instances

open AdequacyArchitecture.Portability

/--
**OG1 grammar** — **NF0** pullback display, **NF1** finite **`G_adm`**, **NF2** certified row, **NF3** upgrade witness.
-/
inductive Program1OuterGateGrammar : Type
  | /-- **NF0** — `U_pullback` -/ uPullback
  | /-- **NF1** — finite admissibility family -/ gAdm
  | /-- **NF2** — `CertifiedFrontierRow` -/ certifiedRowNonempty
  | /-- **NF3** — `CertifiedUpgradeWitness` -/ upgradeNonempty

/--
Interpretation **`Type → Prop`** for each grammar symbol (**Program 1** carriers **`γ : Type`**).
-/
def Program1OuterGateGrammar.interp (g : Program1OuterGateGrammar) (γ : Type) : Prop :=
  match g with
  | .uPullback => Program1AdmissibilityPullbackDisplayWitness γ
  | .gAdm => program1FiniteGAdm γ
  | .certifiedRowNonempty => Nonempty (CertifiedFrontierRow γ)
  | .upgradeNonempty => Nonempty (CertifiedUpgradeWitness γ)

/-- A predicate is **grammar-generated** if it is **pointwise** equivalent to **`interp g`**. -/
abbrev Program1GrammarGeneratedOuterGate (C : Type → Prop) : Prop :=
  ∃ g : Program1OuterGateGrammar, ∀ γ : Type, C γ ↔ g.interp γ

theorem program1FiniteGAdm_of_outerGateGrammar_interp {g : Program1OuterGateGrammar} {γ : Type}
    (h : g.interp γ) : program1FiniteGAdm γ := by
  cases g
  · exact ⟨Program1FiniteGAdm.pullback h⟩
  · exact h
  · exact ⟨Program1FiniteGAdm.pullback
      (program1AdmissibilityPullbackDisplayWitness_of_nonempty_certifiedFrontierRow h)⟩
  · rcases h with ⟨w⟩
    exact ⟨Program1FiniteGAdm.upgradeWitness w⟩

theorem program1AdmissibilityPullbackDisplayWitness_of_outerGateGrammar_interp
    {g : Program1OuterGateGrammar} {γ : Type} (h : g.interp γ) :
    Program1AdmissibilityPullbackDisplayWitness γ :=
  program1FiniteGAdm_implies_program1AdmissibilityPullbackDisplayWitness
    (program1FiniteGAdm_of_outerGateGrammar_interp h)

theorem program1OuterLayerBLaw_of_outerGateGrammar_interp {g : Program1OuterGateGrammar} {γ : Type}
    (h : g.interp γ) : program1OuterLayerBLaw γ :=
  exists_absoluteFrontierRawS1_of_program1FiniteGAdm (program1FiniteGAdm_of_outerGateGrammar_interp h)

theorem Program1OuterCertificateSound_of_grammarGenerated {C : Type → Prop}
    (hGen : Program1GrammarGeneratedOuterGate C) : Program1OuterCertificateSound C := by
  rcases hGen with ⟨g, hφ⟩
  intro γ hc
  have hi := (hφ γ).1 hc
  exact program1OuterLayerBLaw_of_outerGateGrammar_interp hi

theorem program1FiniteGAdm_of_grammarGenerated {C : Type → Prop} (hGen : Program1GrammarGeneratedOuterGate C)
    {γ : Type} (hγ : C γ) : program1FiniteGAdm γ := by
  rcases hGen with ⟨g, hφ⟩
  exact program1FiniteGAdm_of_outerGateGrammar_interp ((hφ γ).1 hγ)

/--
**Grammar-cut Max-A** (`C ⊆ G_adm` for grammar-generated `C`).
-/
theorem program1FiniteGAdm_of_grammarGenerated_any {C : Type → Prop}
    (hGen : Program1GrammarGeneratedOuterGate C) : ∀ γ, C γ → program1FiniteGAdm γ := by
  intro γ hc
  exact program1FiniteGAdm_of_grammarGenerated hGen hc

/--
**Grammar-cut Max-A** (`C ⊆ U_pullback` for grammar-generated `C`; **MU1**).
-/
theorem program1AdmissibilityPullbackDisplayWitness_of_grammarGenerated {C : Type → Prop}
    (hGen : Program1GrammarGeneratedOuterGate C) {γ : Type} (hγ : C γ) :
    Program1AdmissibilityPullbackDisplayWitness γ :=
  program1FiniteGAdm_implies_program1AdmissibilityPullbackDisplayWitness
    (program1FiniteGAdm_of_grammarGenerated hGen hγ)

/--
**OG1 packaging:** soundness is **free** from grammar generation; **maximality** is **`pullback`** **witnesshood**.
-/
theorem program1_outer_grammar_cut_maxA {C : Type → Prop} (hGen : Program1GrammarGeneratedOuterGate C)
    (_hSound : Program1OuterCertificateSound C) {γ : Type} (hγ : C γ) :
    Program1AdmissibilityPullbackDisplayWitness γ :=
  program1AdmissibilityPullbackDisplayWitness_of_grammarGenerated hGen hγ

end AdequacyArchitecture.Instances
