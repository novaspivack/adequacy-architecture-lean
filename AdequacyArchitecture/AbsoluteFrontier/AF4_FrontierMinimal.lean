/-
  **SPEC_027_QX9 — Phase AF-4:** obstruction / hypothesis **minimization**.

  **`HFrontier`** is already **3-field minimal** (`β`, `slot`, `slot_ok`): there is **no** duplicated `HFinal`
  hypothesis — **`hf`** is **abbrev**-derived from **`slot.lawful`**, so any redundant packaging would introduce
  proof obligations **`slot.lawful = hf`** with **no** strengthening.

  **`FrontierSlotWitness`** is **defeq-equivalent** to **`HFrontier`** (round-trip **`rfl`**) — the only elidable
  layer is naming.
-/

import AdequacyArchitecture.AbsoluteFrontier.AF3_HFrontier
import AdequacyArchitecture.Summit.SummitOverClass

namespace AdequacyArchitecture.AbsoluteFrontier

universe u v

open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open AdequacyArchitecture.Summit

variable {α : Type u}

/-- AF-4:** `hf` **is** `slot.lawful` (no separate spine field). -/
@[simp] theorem HFrontier.hf_eq_slot_lawful (H : HFrontier α) : H.hf = H.slot.lawful :=
  rfl

/-- Eliminable isomorphic packaging (identity maps). -/
structure FrontierSlotWitness (α : Type u) where
  β : Type v
  slot : SemanticLiftCertificateSlot α β
  ok : SemanticLiftCertificateSatisfied slot

def FrontierSlotWitness.toHFrontier (w : FrontierSlotWitness α) : HFrontier α :=
  { β := w.β, slot := w.slot, slot_ok := w.ok }

def HFrontier.toSlotWitness (H : HFrontier α) : FrontierSlotWitness α :=
  { β := H.β, slot := H.slot, ok := H.slot_ok }

theorem FrontierSlotWitness.roundtrip (H : HFrontier α) :
    H.toSlotWitness.toHFrontier = H :=
  rfl

theorem FrontierSlotWitness.roundtrip' (w : FrontierSlotWitness α) :
    w.toHFrontier.toSlotWitness = w :=
  rfl

/-- **Compressed over-class statement** (single `∧` chain, no nested duplicate `HFinal`). -/
theorem hFrontier_compressed (H : HFrontier α) :
    MasterStratifiedAdequacyCascadeAt H.slot.lawful.𝔠 H.slot.lawful.P H.slot.lawful.rcp ∧
      SemanticLiftCertificateSatisfied H.slot ∧
      SummitS1AtLawful H.slot.lawful.𝔠.strat.outer :=
  hFrontier_over_class_bundle H

end AdequacyArchitecture.AbsoluteFrontier
