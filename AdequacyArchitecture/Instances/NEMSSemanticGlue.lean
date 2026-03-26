/-
  **SPEC_025 — NEMS semantic glue** (explicit alignment vocabulary + halting linkage + obstructions).

  **`NEMSSemanticBridgeFrontier`** isolates **orthogonal signatures**; this module adds **positive** glue
  (`NEMStrongSemanticGlue`, `NEMAnchoredSemanticGlue`), the **halting** existential linkage
  (`Truth` grid ↔ `asr.RT`), and **obstructions** to reading default bridge witnesses as global
  “account ↔ semantic inhabitation” predicates on **`Framework`**.

  **Summit packaging:** `NEMSFinalSummitSemanticGlue.lean` (`HFinal` + anchored glue);
  **`NEMSSemanticTracking.lean`** (Phase B uniform extraction); **`NEMSFinalSummitLinkedReporting.lean`**
  (Phase C reporting package + linked shapes); **`NEMSSemanticReportCertificate.lean`** (Phase D indexed
  certificates across the lawful / EPIC_018 seam); **`NEMSSemanticReportCertificateTransport.lean`**
  (Phase E observation span + phantom-index reindex). **Phase F:** canonical **`rfl`** agreement
  (`halting_anchored_canonical_certificate_summit_agreement` in `NEMSSemanticReportCertificate.lean`).
-/

import AdequacyArchitecture.Core.Basic
import AdequacyArchitecture.Instances.NEMSFrameworkBridgeRecord
import AdequacyArchitecture.Instances.NEMSFaithful
import AdequacyArchitecture.Instances.NEMSBridgeReflexiveAnchor
import AdequacyArchitecture.Instances.NEMSSemanticBridgeFrontier
import AdequacyArchitecture.Lawful.TwoPointLawfulRelocation
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Encodable.Basic

namespace AdequacyArchitecture.Instances

open AdequacyArchitecture.Lawful
open ReflexiveArchitecture
open ReflexiveArchitecture.Instances
open Nat.Partrec (Code)
open Nat.Partrec.Code
open NemS
open NemS.Framework
open NemS.MFRR
open NemS.Physical

/-! ### Witness predicates (semantic grid vs coded `RT`) -/

/-- Some `Truth` instance (`Model × Rec` grid). -/
def ExistentialTruthWitness (F : Framework) : Prop :=
  ∃ m : F.Model, ∃ r : F.Rec, F.Truth m r

/-- Some coded record-truth value at the packaged **ASR** / **PhysUCT** axis. -/
def ExistentialRTWitness (F : Framework) [inst : DiagonalCapable F] : Prop :=
  ∃ n : ℕ, inst.asr.RT n

/-! ### Glue structures -/

/-- **Strong semantic glue** at anchor `F`: `P.final` + bi-interpretability of `A F` with both witness forms. -/
structure NEMStrongSemanticGlue (F : Framework) [DiagonalCapable F]
    (P : AdequacyPredicates Framework) (A : Account Framework) : Prop where
  final : P.adeq AdeqMode.final A
  account_iff_truth : A F ↔ ExistentialTruthWitness F
  account_iff_rt : A F ↔ ExistentialRTWitness F

/-- **`A F` true** + strong glue — enough to extract existential witnesses at `F`. -/
structure NEMAnchoredSemanticGlue (F : Framework) [DiagonalCapable F]
    (P : AdequacyPredicates Framework) (A : Account Framework) : Prop where
  glue : NEMStrongSemanticGlue F P A
  anchor_holds : A F

theorem existential_truth_of_anchored {F : Framework} [DiagonalCapable F]
    {P : AdequacyPredicates Framework} {A : Account Framework}
    (h : NEMAnchoredSemanticGlue F P A) : ExistentialTruthWitness F :=
  h.glue.account_iff_truth.mp h.anchor_holds

theorem existential_rt_of_anchored {F : Framework} [DiagonalCapable F]
    {P : AdequacyPredicates Framework} {A : Account Framework}
    (h : NEMAnchoredSemanticGlue F P A) : ExistentialRTWitness F :=
  h.glue.account_iff_rt.mp h.anchor_holds

/-! ### Halting grid — existential **`Truth` ↔ ∃ `RT`** (`SPEC_025` / `Instantiation`) -/

theorem halting_existential_truth_iff_existential_rt :
    ExistentialTruthWitness haltingFramework ↔
      @ExistentialRTWitness haltingFramework haltingFramework_diagonalCapable :=
  haltingFramework_exists_truth_iff_exists_asr_rt

theorem existential_truth_witness_haltingFramework : ExistentialTruthWitness haltingFramework := by
  refine ⟨Encodable.encode Code.zero, (0 : ℕ), ?_⟩
  rw [haltingFramework_truth_eq_eval_dom]
  simpa [Denumerable.ofNat_encode] using
    (show (eval Code.zero (0 : ℕ)).Dom by
      have : eval Code.zero (0 : ℕ) = Part.some 0 := rfl
      rw [this]; trivial)

/-- `Fin 2` grid with **`Truth := ⊤`** — carries **existential** semantic witnesses but is **not** the halting
(`ℕ × ℕ`) framework (obstruction to globally identifying `distinguishingEqAccount halting` with
`ExistentialTruthWitness`). -/
def semanticGlueObstructionFramework : Framework where
  Model := Fin 2
  Rec := Fin 2
  Truth := fun _ _ => True

private theorem nat_ne_fin2_for_semantic_glue : (ℕ : Type) ≠ Fin 2 := fun h => by
  have hi : Infinite ℕ := inferInstance
  have _ : Infinite (Fin 2) := h ▸ hi
  have : Finite (Fin 2) := inferInstance
  exact not_finite (Fin 2)

theorem semanticGlueObstructionFramework_ne_haltingFramework :
    semanticGlueObstructionFramework ≠ haltingFramework := fun h =>
  nat_ne_fin2_for_semantic_glue (congrArg (·.Model) h).symm

theorem existential_truth_witness_semanticGlueObstructionFramework :
    ExistentialTruthWitness semanticGlueObstructionFramework :=
  ⟨⟨0, by decide⟩, ⟨0, by decide⟩, trivial⟩

/-! ### Obstruction — packaged `distinguishingEqAccount` is not a **global** truth-witness classifier -/

theorem not_forall_framework_truth_iff_distinguishing_semantic_pair_i1 :
    ¬ (∀ F : Framework, distinguishingEqAccount nemsSemanticPairI1 F ↔ ExistentialTruthWitness F) := by
  intro h
  have ht := existential_truth_witness_haltingFramework
  have hiff := h haltingFramework
  have hnEq : ¬ nemsSemanticPairI0 = nemsSemanticPairI1 :=
    fun he => haltingFramework_ne_fin2HaltingCodeFramework he
  have hA : ¬ distinguishingEqAccount nemsSemanticPairI1 haltingFramework := by
    intro he
    simpa [distinguishingEqAccount, nemsSemanticPairI0, nemsSemanticPairI1] using hnEq he
  exact hA (hiff.mpr ht)

theorem not_forall_framework_truth_iff_distinguishing_semantic_pair_i0 :
    ¬ (∀ F : Framework, distinguishingEqAccount nemsSemanticPairI0 F ↔ ExistentialTruthWitness F) := by
  intro h
  have ht := existential_truth_witness_semanticGlueObstructionFramework
  have hiff := h semanticGlueObstructionFramework
  have hA : ¬ distinguishingEqAccount nemsSemanticPairI0 semanticGlueObstructionFramework := by
    intro he
    simp [distinguishingEqAccount, nemsSemanticPairI0] at he
    exact semanticGlueObstructionFramework_ne_haltingFramework he
  exact hA (hiff.mpr ht)

/-! ### Outer remainder (EPIC_018) — named alias for “semantic bite” storytelling -/

theorem faithful_halting_outer_semanticRemainder_holds :
    faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit := by
  rw [faithful_halting_reflexive_semanticRemainder_unit]
  exact NemS.MFRR.diagonal_barrier_rt haltingFramework (dc := haltingFramework_diagonalCapable)

theorem faithful_halting_outer_semanticRemainder_iff_notComputableRT :
    faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit ↔
      ¬ ComputablePred haltingFramework_diagonalCapable.asr.RT := by
  rfl

end AdequacyArchitecture.Instances
