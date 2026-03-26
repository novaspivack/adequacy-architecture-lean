/-
  **SPEC_027_QX9 — Phase AF-5:** **absolute-frontier apex** interface (honest triage).

  **Proved band (this epic):**
  * **`HFrontier`** over-class packaging (**AF-3**) + minimization (**AF-4**).
  * Certified semantic-lift **schema** (**AF-2**) with **NEMS** recovery and **IC** corpus bypass hook.

  **Proved obstructions (pre-existing + packaged):**
  * Native **`HFinal`** on **`icNemsSpineCompressionCarrier`** **iff** full spine data (**AF-1** / **SPEC_026**).
  * Raw **`AbsoluteFrontier*`** targets remain **undefeated** as global theorems — see **`FinalConditionalSummit`**
    Layer B (`def`s, not theorems).

  **Open beyond this apex:** unconditional **`∀ 𝔠, HFrontier …`**, universal semantic transport off the NEMS/hyper
  specialized spine, and lowering **`AbsoluteFrontierRawS1` / `RawS2` / `LawfulS2`** without new lawful classes.
-/

import AdequacyArchitecture.AbsoluteFrontier.AF4_FrontierMinimal
import AdequacyArchitecture.Lawful.FinalConditionalSummit
import AdequacyArchitecture.Summit.SummitOverClass

namespace AdequacyArchitecture.AbsoluteFrontier

universe u

open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open AdequacyArchitecture.Summit

/-- Advisor-facing triage (Lean **data** for spec tables / codegen — not a decidable classifier). -/
inductive AbsoluteFrontierApexKind where
  | provedOverClass
  | provedObstruction
  | openBeyond

/-- Singleton witness recording the **current** apex posture for **SPEC_027**. -/
def apexPostSPEC027 : AbsoluteFrontierApexKind :=
  AbsoluteFrontierApexKind.provedOverClass

/-- **Canonical apex theorem** — every **`HFrontier`** yields the Layer A master cascade. -/
theorem apex_master_cascade_from_hFrontier {α : Type u} (H : HFrontier α) :
    MasterStratifiedAdequacyCascadeAt H.hf.𝔠 H.hf.P H.hf.rcp :=
  hFrontier_highest_summit H

/-- **Canonical apex corollary** — irreducible burden (S1 shape) at the outer law package. -/
theorem apex_summit_irreducible_from_hFrontier {α : Type u} (H : HFrontier α) :
    SummitS1AtLawful H.hf.𝔠.strat.outer :=
  hFrontier_summit_irreducible H

/-- **Re-export** — `AbsoluteFrontierRawS1` (**not** a theorem; still conjecture-shaped). -/
abbrev Apex_AbsoluteFrontierRawS1 (α : Type u) (P : AdequacyPredicates α) (B : BurdenPredicates α) : Prop :=
  AbsoluteFrontierRawS1 P B

/-! For **`AbsoluteFrontierRawS2`** / **`AbsoluteFrontierLawfulS2`**, use **`FinalConditionalSummit`**
  names directly — they close over **`{α}`** from that module’s section and do not abbrev cleanly here. -/

end AdequacyArchitecture.AbsoluteFrontier
