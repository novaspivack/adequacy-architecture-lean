/-
  **SPEC_040_MA1 — Maximality theorem summit (Lean scaffolding).**

  **Paper target (Max-A):** for outer predicates `C : Type → Prop` that are *admissible* under the N1–N5 discipline
  and *sound* for the Program 1 layer-B law, one wants `∀ γ, C γ → Program1AdmissibilityPullbackDisplayWitness γ`.

  **MU1 collapse:** `program1FiniteGAdm γ ↔ Program1AdmissibilityPullbackDisplayWitness γ`, so the mathematical
  residuum is `Admissible C ∧ Sound C ⇒ ∀ γ, C γ → program1FiniteGAdm γ`.

  **This module:** encodes **`Law_B`**, **`Sound`**, the **proved reduction** `C ⊆ G_adm ⇒ C ⊆ U_pullback`, and
  schematic composition under the **certified-row** normal form.
-/

import AdequacyArchitecture.Instances.Program1MetaUnificationMU1

namespace AdequacyArchitecture.Instances

open AdequacyArchitecture.Burden
open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open AdequacyArchitecture.Portability

/-- Program 1 **layer-B law** targets: **∃** `P B`, **`AbsoluteFrontierRawS1 P B`** on the carrier. -/
abbrev program1OuterLayerBLaw (γ : Type) : Prop :=
  ∃ (P : AdequacyPredicates γ) (B : BurdenPredicates γ), AbsoluteFrontierRawS1 P B

/-- An outer certificate class `C` is **sound** when it implies the layer-B law on every carrier. -/
abbrev Program1OuterCertificateSound (C : Type → Prop) : Prop :=
  ∀ {γ : Type}, C γ → program1OuterLayerBLaw γ

theorem program1_outer_sound_of_compact_under_finiteGAdm {C : Type → Prop}
    (h : ∀ γ, C γ → program1FiniteGAdm γ) : Program1OuterCertificateSound C := by
  intro γ hc
  exact exists_absoluteFrontierRawS1_of_program1FiniteGAdm (h γ hc)

/--
**Max-A reduction step (MU1):** if `C` is **contained in** finite **`G_adm`**, then `C` is **contained in**
**`U_pullback`**.
-/
theorem program1AdmissibilityPullbackDisplayWitness_of_maps_under_finiteGAdm {C : Type → Prop}
    (h : ∀ γ, C γ → program1FiniteGAdm γ) {γ : Type} (hc : C γ) :
    Program1AdmissibilityPullbackDisplayWitness γ :=
  program1FiniteGAdm_implies_program1AdmissibilityPullbackDisplayWitness (h γ hc)

/--
**Normal form NF2** composition: a uniform implication `C γ → Nonempty (CertifiedFrontierRow γ)` yields
**`U_pullback`** via SPEC_039 / MU1 packaging.
-/
theorem program1AdmissibilityPullbackDisplayWitness_of_maps_under_nonempty_certifiedFrontierRow
    {C : Type → Prop} (h : ∀ γ, C γ → Nonempty (CertifiedFrontierRow γ)) {γ : Type} (hc : C γ) :
    Program1AdmissibilityPullbackDisplayWitness γ :=
  program1AdmissibilityPullbackDisplayWitness_of_nonempty_certifiedFrontierRow (h γ hc)

/-! ## SPEC_044_NF4_CUT — NF4 (**`S1Lawful`**-only) vs **`G_adm` / `U_pullback`** (boundary) -/

/-- **NF4-shaped** hypothesis: **`Nonempty (S1LawfulFrontierRow γ)`** (**MA1** **NF4** **menu** **)** **.-/
abbrev program1OuterWinS1LawfulNonempty : Type → Prop :=
  fun γ => Nonempty (S1LawfulFrontierRow γ)

/--
**NF4-Q2** **(**Lean** **anchor** **)** **:** **pure** **Stage-B** **nonemptiness** **implies** **`program1OuterLayerBLaw`**
**(**∃** **`P,B`**,** **`AbsoluteFrontierRawS1` ** **)** **—** **so** **`Program1OuterCertificateSound`** **holds** **. ** **OG1** **grammar** **deliberately** **omits** **this** **as** **a** **generator** **(**NF4** **hazard** **)** **;** **no** **automatic** **collapse** **to** **`program1FiniteGAdm`** **is** **proved** **here** **.-/
theorem Program1OuterCertificateSound_program1OuterWinS1LawfulNonempty :
    Program1OuterCertificateSound program1OuterWinS1LawfulNonempty := by
  intro γ h
  rcases h with ⟨row⟩
  exact ⟨row.lawful.P, row.lawful.B, absoluteFrontierRawS1_of_s1LawfulFrontierRow row⟩

end AdequacyArchitecture.Instances
