/-
  **SPEC_024 — semantic vs bridge-core frontier (bookkeeping + sharp typing).**

  Level **3b** bridge row packages **non-vacuous finality** as inequality of some
  `A : Framework → Prop` at two concrete frameworks. EPIC_018 **`concreteNEMSReflexiveLayer`**
  packages **outer** predicates from **`DiagonalCapable.asr.RT : ℕ → Prop`**, not from
  `Framework.Truth` on `Model × Rec`.

  This module is a **formal guardrail:** these signatures are **orthogonal** unless one adds an
  explicit morphism or enriched account discipline tying `A` to `Truth` / coded `RT`.
-/

import AdequacyArchitecture.Core.Basic
import AdequacyArchitecture.Instances.NEMSBridgeReflexiveAnchor
import AdequacyArchitecture.Lawful.TwoPointLawfulRelocation

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

/-! ### `Truth` shape on the Level 3b pair (halting grid vs `Fin 2` slice) -/

theorem haltingFramework_truth_eq_eval_dom (m r : ℕ) :
    haltingFramework.Truth m r = (eval (Denumerable.ofNat Code m) r).Dom :=
  rfl

theorem fin2HaltingCodeFramework_truth_eq_eval_dom (m r : Fin 2) :
    fin2HaltingCodeFramework.Truth m r =
      (eval (Denumerable.ofNat Code m.val) r.val).Dom :=
  rfl

/-! ### Bridge-core finality = propositional inequality at the named framework values -/

theorem nemsFrameworkSemanticPairNonVacuousFinalAdequacy_final_iff (A : Account Framework) :
    nemsFrameworkSemanticPairNonVacuousFinalAdequacy.adeq AdeqMode.final A ↔
      A nemsSemanticPairI0 ≠ A nemsSemanticPairI1 := by
  simp [nemsFrameworkSemanticPairNonVacuousFinalAdequacy]

theorem distinguishingEqAccount_nemsSemanticPairI0 (F : Framework) :
    distinguishingEqAccount nemsSemanticPairI0 F = (F = nemsSemanticPairI0) :=
  rfl

/-! ### Faithful outer layer fields reduce to **ASR.RT** (ℕ-indexed), not `Framework.Truth` -/

theorem faithful_halting_reflexive_totalOn_unit :
    faithfulNEMSHaltingReflexiveLayer.TotalOn PUnit.unit =
      ComputablePred haltingFramework_diagonalCapable.asr.RT :=
  rfl

theorem faithful_halting_reflexive_semanticRemainder_unit :
    faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit =
      ¬ ComputablePred haltingFramework_diagonalCapable.asr.RT :=
  rfl

theorem faithful_halting_reflexive_finalSelfTheory_unit :
    faithfulNEMSHaltingReflexiveLayer.FinalSelfTheory PUnit.unit =
      ComputablePred haltingFramework_diagonalCapable.asr.RT :=
  rfl

variable (F : Framework) [dc : DiagonalCapable F]

theorem concrete_nems_reflexive_totalOn_unit :
    (concreteNEMSReflexiveLayer F (dc := dc)).TotalOn PUnit.unit =
      ComputablePred dc.asr.RT :=
  rfl

theorem concrete_nems_reflexive_semanticRemainder_unit :
    (concreteNEMSReflexiveLayer F (dc := dc)).SemanticRemainder PUnit.unit =
      ¬ ComputablePred dc.asr.RT :=
  rfl

theorem concrete_nems_reflexive_finalSelfTheory_unit :
    (concreteNEMSReflexiveLayer F (dc := dc)).FinalSelfTheory PUnit.unit =
      ComputablePred dc.asr.RT :=
  rfl

end AdequacyArchitecture.Instances
