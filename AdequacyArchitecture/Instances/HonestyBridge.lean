/-
  **Honesty bridge** — how the main corpus **tracks** relate (read before identifying them).

  1. **`LinkedLayer` (`linkedCorpusArchitecture`):** `LinkedArchitecture Unit` from
     `ReflexiveArchitecture.Instances.CrossCorpusInstance`. Inner `EnrichedIrreducibility` is
     **definitionally** tied to the outer remainder existential (`Iff.rfl` on `BarrierProp`).
     Abstract **barrier** / definitional non-erasure packaging.

  2. **`FaithfulCorpusJoint` (`faithful_joint_strata_from_sources`):** from
     `ReflexiveArchitecture.Bridge.DirectCrossCorpusBridge` — **joint satisfaction** of
     (a) NEMS `SemanticRemainder` on `haltingFramework` and (b) IC `EnrichedIrreducibility` on the
     NEMS spine, proved from **separate** corpus theorems. Strata states that these are **not**
     logically equivalent; the honest shape is a **conjunction** (`nems_spine_both_strata`),
     not a biconditional across domains.

  3. **`CorpusDischarge` (`Fin 2`):** Nonempty three Strata interfaces with **minimal** hypotheses —
     a **different** carrier and proof story from (1) and (2).

  **Why separate lemmas here:** Packaging the joint statement with `∧` or projecting `.1`/`.2` in a
  single Adequacy declaration hits **universe metavariables** on mixed `Outer`/`Inner` polymorphism
  (`FaithfulCorpusJoint` module doc). The two theorems below are exactly the **proof terms** Strata
  uses for `nems_spine_strata_from_sources` (hence for `faithful_joint_strata_from_sources`), split
  into named Adequacy theorems without fragile projections.

  **Unified carrier scope (morphisms, not identification):** `UnifiedCarrierMorphisms.lean` and
  **`SPEC_014_UC1`** — terminal collapse `Fin 2 → Unit`, injective `Fin 2 ↪ ℕ`, and explicit **non-goals**
  for `Framework` / spine indices.
-/

import AdequacyArchitecture.Instances.FaithfulCorpusJoint

namespace AdequacyArchitecture.Instances

open ReflexiveArchitecture.Bridge
open ReflexiveArchitecture.Instances
open NemS.Diagonal
open InfinityCompression.MetaProof
open InfinityCompression.Meta

/-- First conjunct of Strata `nems_spine_strata_from_sources` (alias `faithful_joint_strata_from_sources`):
NEMS outer `SemanticRemainder` on `haltingFramework` (`haltingFrameworkDC`). Same proof term as
`nems_halting_semantic_remainder` (`diagonal_barrier_rt haltingFramework`). -/
theorem faithful_joint_strata_outer_semantic_remainder :
    (concreteNEMSReflexiveLayer haltingFramework (dc := haltingFrameworkDC)).SemanticRemainder PUnit.unit :=
  nems_halting_semantic_remainder

/-- Second conjunct: IC inner `EnrichedIrreducibility` on the NEMS spine. Same proof as the second
component of `nems_spine_strata_from_sources`. -/
theorem faithful_joint_strata_inner_enriched_irreducibility :
    (concreteICCertificationLayer nemsSpineChain.toArchitecture
        (librarySummitExtraction nemsSpineChain.toArchitecture)
        nemsRoleSkeleton_1_0 nemsRoleSkeleton_3_2
        nems_role_skeletons_ne).EnrichedIrreducibility :=
  concreteIC_enrichedIrrHolds
    (librarySummitExtraction nemsSpineChain.toArchitecture)
    nemsRoleSkeleton_1_0 nemsRoleSkeleton_3_2
    nems_role_skeletons_ne

end AdequacyArchitecture.Instances
