/-
  **SPEC_027_QX9 — Phase AF-2 (NEMS recovery):** halting-anchored master bundle as **`SemanticLiftCertificateSlot`**.

  **`companionObligations := True`** here: **SPEC_025** already documents that **`SemanticRemainder`** and similar
  sibling facts must be cited **compositionally** next to the master **`Type`** bundle — not omitted, only **not**
  forced into the same **`structure`** fields (sort discipline).
-/

import AdequacyArchitecture.AbsoluteFrontier.AF2_SemanticLiftCertificate
import AdequacyArchitecture.Instances.NEMSSemanticFaithfulSummitMaster

namespace AdequacyArchitecture.AbsoluteFrontier

open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open AdequacyArchitecture.Instances
open HaltingAnchoredFaithfulSummitMasterBundle
open NemS
open NemS.Framework
open NemS.Physical

universe u

variable {h : HFinalFrameworkWithNEMAnchoredGlue} {hF : h.F₀ = haltingFramework}

/--
`NEMSHaltingSummitSemanticCertificate` is a **`structure : Prop`**; AF-2 needs a **`Type`** certificate carrier,
so we use a **one-field type** witness (`proof-irrelevant` content stays in the **Prop** field of the source cert).
-/
structure NemsHaltingAnchoredCertWitness (h : HFinalFrameworkWithNEMAnchoredGlue)
    (hF : h.F₀ = haltingFramework) : Type where
  cert : NEMSHaltingSummitSemanticCertificate h hF

/-- NEMS halting-anchored slot. -/
def nemsHaltingAnchoredSemanticLiftSlot (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    SemanticLiftCertificateSlot Framework (NemsHaltingAnchoredCertWitness h hF) where
  lawful := h.toHFinal
  native := { cert := b.summitCert }
  certificateClaims :=
    (b.summitCert.summitTracked = halting_anchored_glued_summit_semantic_report h hF) ∧ True

theorem nems_haltingAnchored_slot_satisfied (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    SemanticLiftCertificateSatisfied (nemsHaltingAnchoredSemanticLiftSlot b) :=
  And.intro b.summit_agrees trivial

theorem nems_haltingAnchored_certified_cascade (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    MasterStratifiedAdequacyCascadeAt h.𝔠 h.P h.rcp :=
  certified_summit_cascade_of_slot _ (nems_haltingAnchored_slot_satisfied b)

/-- **Semantic report** value carried by the certificate (NEMS branch). -/
def nems_haltingAnchored_summitReport (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    HaltingAnchoredGluedSummitSemanticReport h hF :=
  agreed_summit b

theorem nems_haltingAnchored_coherence_eq (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) :
    (nemsHaltingAnchoredSemanticLiftSlot b).native.cert.summitTracked =
      halting_anchored_glued_summit_semantic_report h hF :=
  b.summit_agrees

end AdequacyArchitecture.AbsoluteFrontier
