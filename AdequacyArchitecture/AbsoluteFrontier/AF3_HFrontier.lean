/-
  **SPEC_027_QX9 — Phase AF-3:** **`HFrontier`** — minimal honest over-class **above bare `HFinal`**.

  **Mathematical content:** a witness that a branch supplies **both** a lawful Layer A row **and** a **certified**
  semantic-lift slot satisfying **`SemanticLiftCertificateSatisfied`**. This is **strictly** stronger data than
  `HFinal α` alone (must exhibit `NativeCert` + **`Prop`** conjuncts).

  **Not claimed:** every `HFinal` arises from some slot (no **`∀ 𝔠, …`**); **AF-5** records raw **`AbsoluteFrontier*`**
  as still open.
-/

import AdequacyArchitecture.AbsoluteFrontier.AF2_SemanticLiftCertificate
import AdequacyArchitecture.AbsoluteFrontier.AF2_NEMSRecover
import AdequacyArchitecture.AbsoluteFrontier.AF2_ICHook
import AdequacyArchitecture.Summit.SummitOverClass

namespace AdequacyArchitecture.AbsoluteFrontier

open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open AdequacyArchitecture.Summit
open AdequacyArchitecture.Instances
open HaltingAnchoredFaithfulSummitMasterBundle
open NemS
open NemS.Framework
open NemS.Physical

universe u v

/-- Over-class package: satisfied semantic-lift certificate slot on **`α : Type u`** with native cert in **`β : Type v`**. -/
structure HFrontier (α : Type u) where
  β : Type v
  slot : SemanticLiftCertificateSlot α β
  slot_ok : SemanticLiftCertificateSatisfied slot

variable {α : Type u}

/-- Layer A row carried by the frontier witness. -/
abbrev HFrontier.hf (H : HFrontier α) : HFinal α :=
  H.slot.lawful

theorem hFrontier_highest_summit (H : HFrontier α) :
    MasterStratifiedAdequacyCascadeAt H.hf.𝔠 H.hf.P H.hf.rcp :=
  certified_summit_cascade_of_slot H.slot H.slot_ok

theorem hFrontier_summit_irreducible (H : HFrontier α) :
    SummitS1AtLawful H.hf.𝔠.strat.outer :=
  certified_summit_irreducible_of_slot H.slot H.slot_ok

theorem hFrontier_semantic_ok (H : HFrontier α) : SemanticLiftCertificateSatisfied H.slot :=
  H.slot_ok

/-- Bundled **over-class** conclusion: cascade + semantic satisfaction + S1 corollary. -/
theorem hFrontier_over_class_bundle (H : HFrontier α) :
    MasterStratifiedAdequacyCascadeAt H.hf.𝔠 H.hf.P H.hf.rcp ∧
      SemanticLiftCertificateSatisfied H.slot ∧
      SummitS1AtLawful H.hf.𝔠.strat.outer :=
  And.intro (hFrontier_highest_summit H) (And.intro H.slot_ok (hFrontier_summit_irreducible H))

/-! ### Constructors (branch-fed; no raw universality) -/

variable {h : HFinalFrameworkWithNEMAnchoredGlue} {hF : h.F₀ = haltingFramework}

def HFrontier.from_nems_halting_bundle (b : HaltingAnchoredFaithfulSummitMasterBundle h hF) : HFrontier Framework where
  β := NemsHaltingAnchoredCertWitness h hF
  slot := nemsHaltingAnchoredSemanticLiftSlot b
  slot_ok := nems_haltingAnchored_slot_satisfied b

def HFrontier.from_ic_corpus_bypass (w : ICSummitContractBypassWitness) : HFrontier CorpusStrataCarrier where
  β := Unit
  slot := icBypassSemanticLiftSlot w
  slot_ok := ic_bypass_slot_satisfied w

/-- Standard IC bypass hits the packaged **`icCS3HFinal`** row. -/
theorem hFrontier_from_ic_standard_hf :
    (HFrontier.from_ic_corpus_bypass af1_standard_icSummit_contract_bypass).hf = icCS3HFinal :=
  rfl

end AdequacyArchitecture.AbsoluteFrontier
