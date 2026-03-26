/-
  **SPEC_028_EK7 — Stage II (Option D):** branch-agnostic **semantic lift** portability layer.

  **Purpose.** `SemanticLiftCertificateSlot` (**SPEC_027 AF-2**) already separates lawful summit data, native
  certificate, and a single `Prop` of claims. This module adds **outsider-facing** packaging: a certified row,
  named cascade corollaries, and a **branch tag** enum for documentation (not a decidable classifier).

  **Honest boundary.** No new summit strength: theorems are **`exact`** wraps of
  `certified_summit_cascade_of_slot` / `certified_summit_irreducible_of_slot`. -/
import AdequacyArchitecture.AbsoluteFrontier.AF2_SemanticLiftCertificate

universe u v

namespace AdequacyArchitecture.Portability

open AdequacyArchitecture.AbsoluteFrontier
open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open AdequacyArchitecture.Summit

variable {α : Type u}

/-- Advisor / table tag: narrative source of a slot (**data only** — not used in proofs). -/
inductive SemanticLiftBranchTag where
  /-- NEMS halting-anchored faithful master bundle (see `AF2_NEMSRecover`). -/
  | haltingAnchoredNems
  /-- IC corpus bypass with `Unit` native certificate (see `AF2_ICHook`). -/
  | icCorpusBypassUnitNative
  /-- Any other branch-supplied `SemanticLiftCertificateSlot`. -/
  | other

/-- Certified **AF-2** row: slot + proof that `certificateClaims` hold. -/
structure CertifiedSemanticLift (α : Type u) (β : Type v) where
  slot : SemanticLiftCertificateSlot α β
  satisfied : SemanticLiftCertificateSatisfied slot

variable {β : Type v}

abbrev CertifiedSemanticLift.lawful (C : CertifiedSemanticLift α β) : HFinal α :=
  C.slot.lawful

def SemanticLiftCertificateSlot.toCertified {α : Type u} {β : Type v} (s : SemanticLiftCertificateSlot α β)
    (hs : SemanticLiftCertificateSatisfied s) : CertifiedSemanticLift α β :=
  ⟨s, hs⟩

/-- **Public name** — Layer A master cascade from a certified lift (same math as AF-2). -/
theorem public_cascade_of_certified_semantic_lift (C : CertifiedSemanticLift α β) :
    MasterStratifiedAdequacyCascadeAt C.lawful.𝔠 C.lawful.P C.lawful.rcp :=
  certified_summit_cascade_of_slot C.slot C.satisfied

/-- **Public name** — S1-at-lawful-outer from a certified lift (same math as AF-2). -/
theorem public_summit_irreducible_of_certified_semantic_lift (C : CertifiedSemanticLift α β) :
    SummitS1AtLawful C.lawful.𝔠.strat.outer :=
  certified_summit_irreducible_of_slot C.slot C.satisfied

theorem public_over_class_pair_of_certified_semantic_lift (C : CertifiedSemanticLift α β) :
    MasterStratifiedAdequacyCascadeAt C.lawful.𝔠 C.lawful.P C.lawful.rcp ∧
      SummitS1AtLawful C.lawful.𝔠.strat.outer :=
  And.intro (public_cascade_of_certified_semantic_lift C) (public_summit_irreducible_of_certified_semantic_lift C)

end AdequacyArchitecture.Portability
