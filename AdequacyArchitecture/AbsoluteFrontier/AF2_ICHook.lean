/-
  **SPEC_027_QX9 — Phase AF-2 (IC hook):** corpus bypass as a **degenerate** `SemanticLiftCertificateSlot`.

  * **`semanticCoherence := True`:** the honest semantic identification happens on **`CorpusStrataCarrier`** via the
    joint **`nativeCorpusJoint`**, not via a compression-native summit certificate.
  * **Sharp gap:** **`icNemsSpineCompressionCarrier`** still has **no** native `HFinal` / spine in this repo
    (**AF-1** iff); this hook **does not** pretend to patch that with a fake `NativeCert`.
-/

import AdequacyArchitecture.AbsoluteFrontier.AF2_SemanticLiftCertificate
import AdequacyArchitecture.AbsoluteFrontier.AF1_ICNativeSummitFrontier
import AdequacyArchitecture.Instances.CorpusDischarge

namespace AdequacyArchitecture.AbsoluteFrontier

universe u

open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open AdequacyArchitecture.Instances

/-- IC **corpus** entry: claims = trivial semantic marker ∧ SPEC_021 joint. -/
def icBypassSemanticLiftSlot (w : ICSummitContractBypassWitness) :
    SemanticLiftCertificateSlot CorpusStrataCarrier Unit where
  lawful := w.corpusHFinal
  native := ()
  certificateClaims := True ∧ ic_faithful_native_pair_cs3_nv_bridge_core_joint_prop

theorem ic_bypass_slot_satisfied (w : ICSummitContractBypassWitness) :
    SemanticLiftCertificateSatisfied (icBypassSemanticLiftSlot w) :=
  And.intro trivial w.nativeCorpusJoint

theorem ic_standard_bypass_slot_satisfied :
    SemanticLiftCertificateSatisfied (icBypassSemanticLiftSlot af1_standard_icSummit_contract_bypass) :=
  ic_bypass_slot_satisfied _

end AdequacyArchitecture.AbsoluteFrontier
