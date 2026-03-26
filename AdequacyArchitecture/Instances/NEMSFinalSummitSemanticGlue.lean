/-
  **SPEC_025 — Conditional summit + NEMS anchored semantic glue** (Layer A+).

  Extends **`HFinal Framework`** with **`NEMAnchoredSemanticGlue`** at the same `P` summit predicate,
  yielding **witnessed semantic content** at the anchor framework from summit hypotheses alone (no new lawful
  machinery).
-/

import AdequacyArchitecture.Lawful.FinalConditionalSummit
import AdequacyArchitecture.Instances.NEMSSemanticGlue

namespace AdequacyArchitecture.Instances

open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open NemS
open NemS.Framework
open NemS.MFRR
open NemS.Physical

/-- **`HFinal` at `Framework`** plus **anchored strong glue** for the **same** `P` and an explicit account. -/
structure HFinalFrameworkWithNEMAnchoredGlue extends HFinal Framework where
  F₀ : Framework
  dc₀ : DiagonalCapable F₀
  A₀ : Account Framework
  anchored : @NEMAnchoredSemanticGlue F₀ dc₀ P A₀

theorem existential_truth_witness_of_aligned_summit (h : HFinalFrameworkWithNEMAnchoredGlue) :
    ExistentialTruthWitness h.F₀ :=
  @existential_truth_of_anchored h.F₀ h.dc₀ h.P h.A₀ h.anchored

theorem existential_rt_witness_of_aligned_summit (h : HFinalFrameworkWithNEMAnchoredGlue) :
    @ExistentialRTWitness h.F₀ h.dc₀ :=
  @existential_rt_of_anchored h.F₀ h.dc₀ h.P h.A₀ h.anchored

/-- **Layer A+ (SPEC_025):** same **`highestReachable_summit_at`** lawful cascade as `HFinal`, *and* a
**witnessed** NEMS semantic grid fact at the glue anchor (honest “semantic bite”, not definitional collapse). -/
theorem highestReachable_summit_and_existential_truth_witness
    (h : HFinalFrameworkWithNEMAnchoredGlue) :
    MasterStratifiedAdequacyCascadeAt h.𝔠 h.P h.rcp ∧ ExistentialTruthWitness h.F₀ :=
  And.intro (highestReachable_summit_at h.toHFinal) (existential_truth_witness_of_aligned_summit h)

theorem halting_anchor_existential_rt_of_aligned_summit
    (h : HFinalFrameworkWithNEMAnchoredGlue)
    (hF : h.F₀ = haltingFramework) :
    ∃ n : ℕ, haltingFramework_diagonalCapable.asr.RT n :=
  haltingFramework_exists_truth_iff_exists_asr_rt.mp
    (hF ▸ existential_truth_witness_of_aligned_summit h)

end AdequacyArchitecture.Instances
