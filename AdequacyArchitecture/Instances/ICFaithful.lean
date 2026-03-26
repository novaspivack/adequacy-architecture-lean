/-
  Faithful IC inner layer on the **NEMS spine architecture** (`InfinityCompression.Meta.nemsSpineChain`).

  `ReflexiveArchitecture.Instances.concreteICCertificationLayer` packages IC corpus theorems
  (reflective split, route necessity, T-C+.7-style enriched multiplicity) into
  `Inner.CertificationLayer (CompressionArchitecture …)`. Parameters are the canonical spine
  witnesses used in `ReflexiveArchitecture.Bridge.DirectCrossCorpusBridge`.

  The `Fin 2` corpus corridor (`CorpusDischarge.lean`) remains the toy alignment; this module is the
  **IC-native** Strata index on the same spine carrier as the cross-corpus bridge.

  **`nemsSpineChain_altTerminal`** — second **native** `CompressionArchitecture` (same length; terminal polarity
  flipped); see `InfinityCompression.Meta.nems_spine_architecture_ne_altTerminal` and
  `UnifiedCarrierMorphisms.lean` for the inequality vs the canonical spine.
-/

import ReflexiveArchitecture.Instances.ConcreteFromIC
import InfinityCompression.MetaProof.NonPackagingConstruction
import InfinityCompression.MetaProof.RoleSeparatedSkeleton

namespace AdequacyArchitecture.Instances

open ReflexiveArchitecture
open ReflexiveArchitecture.Instances
open InfinityCompression.MetaProof
open InfinityCompression.Meta

@[reducible]
noncomputable def faithfulICNEMSSpineCertificationLayer :
    ReflexiveArchitecture.Inner.CertificationLayer
      (CompressionArchitecture Unit nemsSpineChain.steps.length) :=
  concreteICCertificationLayer
    nemsSpineChain.toArchitecture
    (librarySummitExtraction nemsSpineChain.toArchitecture)
    nemsRoleSkeleton_1_0 nemsRoleSkeleton_3_2
    nems_role_skeletons_ne

theorem nonempty_faithful_ic_nems_spine_certification_layer :
    Nonempty
      (ReflexiveArchitecture.Inner.CertificationLayer
        (CompressionArchitecture Unit nemsSpineChain.steps.length)) :=
  ⟨faithfulICNEMSSpineCertificationLayer⟩

theorem faithful_ic_nems_spine_enriched_irreducibility_holds :
    faithfulICNEMSSpineCertificationLayer.EnrichedIrreducibility :=
  concreteIC_enrichedIrrHolds
    (librarySummitExtraction nemsSpineChain.toArchitecture)
    nemsRoleSkeleton_1_0 nemsRoleSkeleton_3_2
    nems_role_skeletons_ne

theorem faithful_ic_nems_spine_canonical_bare_certificate_holds :
    faithfulICNEMSSpineCertificationLayer.CanonicalBareCertificate :=
  concreteIC_canonicalBareCertHolds
    (librarySummitExtraction nemsSpineChain.toArchitecture)
    nemsRoleSkeleton_1_0 nemsRoleSkeleton_3_2
    nems_role_skeletons_ne

@[reducible]
noncomputable def faithfulICNEMSAltTerminalCertificationLayer :
    ReflexiveArchitecture.Inner.CertificationLayer
      (CompressionArchitecture Unit nemsSpineChain_altTerminal.steps.length) :=
  concreteICCertificationLayer
    nemsSpineChain_altTerminal.toArchitecture
    (librarySummitExtraction nemsSpineChain_altTerminal.toArchitecture)
    nemsAltTerminalRoleSkeleton_1_0 nemsAltTerminalRoleSkeleton_3_2
    nems_alt_terminal_role_skeletons_ne

theorem nonempty_faithful_ic_nems_alt_terminal_certification_layer :
    Nonempty
      (ReflexiveArchitecture.Inner.CertificationLayer
        (CompressionArchitecture Unit nemsSpineChain_altTerminal.steps.length)) :=
  ⟨faithfulICNEMSAltTerminalCertificationLayer⟩

theorem faithful_ic_nems_alt_terminal_enriched_irreducibility_holds :
    faithfulICNEMSAltTerminalCertificationLayer.EnrichedIrreducibility :=
  concreteIC_enrichedIrrHolds
    (librarySummitExtraction nemsSpineChain_altTerminal.toArchitecture)
    nemsAltTerminalRoleSkeleton_1_0 nemsAltTerminalRoleSkeleton_3_2
    nems_alt_terminal_role_skeletons_ne

theorem faithful_ic_nems_alt_terminal_canonical_bare_certificate_holds :
    faithfulICNEMSAltTerminalCertificationLayer.CanonicalBareCertificate :=
  concreteIC_canonicalBareCertHolds
    (librarySummitExtraction nemsSpineChain_altTerminal.toArchitecture)
    nemsAltTerminalRoleSkeleton_1_0 nemsAltTerminalRoleSkeleton_3_2
    nems_alt_terminal_role_skeletons_ne

end AdequacyArchitecture.Instances
