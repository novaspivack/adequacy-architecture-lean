/-
  **SPEC_028_EK7 — Stage II (Options D + E):** **`HFrontier`** and **apex** as **portable** entry points.

  **`CertifiedSemanticLift`** carries the same data as **`HFrontier`** (native type `β`, slot, satisfaction).
  This file makes the bijection explicit and re-exports **apex** theorems under **public** names for readers
  who start from “certified semantic lift” rather than **AF-3** naming. -/
import AdequacyArchitecture.Portability.SemanticLiftPortability
import AdequacyArchitecture.AbsoluteFrontier.AF5_Apex

universe u v

namespace AdequacyArchitecture.Portability

open AdequacyArchitecture.AbsoluteFrontier
open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open AdequacyArchitecture.Summit

variable {α : Type u} {β : Type v}

/-- Repackage a certified lift as **`HFrontier`** (DEF-iso; see roundtrip lemmas). -/
def CertifiedSemanticLift.toHFrontier (C : CertifiedSemanticLift α β) : HFrontier α where
  β := β
  slot := C.slot
  slot_ok := C.satisfied

def certifiedSemanticLiftOfHFrontier (H : HFrontier α) : CertifiedSemanticLift α H.β :=
  ⟨H.slot, H.slot_ok⟩

@[simp] theorem CertifiedSemanticLift.toHFrontier_slot (C : CertifiedSemanticLift α β) :
    C.toHFrontier.slot = C.slot :=
  rfl

@[simp] theorem CertifiedSemanticLift.toHFrontier_hf (C : CertifiedSemanticLift α β) :
    C.toHFrontier.hf = C.lawful :=
  rfl

theorem CertifiedSemanticLift.toHFrontier_certified_roundtrip (C : CertifiedSemanticLift α β) :
    certifiedSemanticLiftOfHFrontier C.toHFrontier = C := rfl

theorem certifiedSemanticLiftOfHFrontier_roundtrip (H : HFrontier α) :
    (certifiedSemanticLiftOfHFrontier H).toHFrontier = H := rfl

/-- Apex cascade — packaged from certified lift (**=** `public_cascade_of_certified_semantic_lift`). -/
theorem public_apex_master_cascade_from_certified (C : CertifiedSemanticLift α β) :
    MasterStratifiedAdequacyCascadeAt C.lawful.𝔠 C.lawful.P C.lawful.rcp :=
  apex_master_cascade_from_hFrontier C.toHFrontier

theorem public_apex_summit_irreducible_from_certified (C : CertifiedSemanticLift α β) :
    SummitS1AtLawful C.lawful.𝔠.strat.outer :=
  apex_summit_irreducible_from_hFrontier C.toHFrontier

end AdequacyArchitecture.Portability