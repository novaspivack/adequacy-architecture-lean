/-
  **SPEC_024 — EPIC_018 alignment anchor (bookkeeping, not a new bridge theorem).**

  `NEMSFaithful.lean` fixes the faithful outer discharge at **`concreteNEMSReflexiveLayer haltingFramework`**.
  `NEMSFrameworkBridgeRecord.lean` packages bridge-core rows on the **same** native index type `NemS.Framework`.

  This module states definitional / equality facts so “reflexive parameter” vs “semantic-pair witness” cannot be
  conflated without proof.

  **Orthogonality of bridge `P.final` vs outer `Truth`/`RT` signatures:** `Instances/NEMSSemanticBridgeFrontier.lean`.
-/

import AdequacyArchitecture.Instances.NEMSFaithful
import AdequacyArchitecture.Instances.NEMSFrameworkBridgeRecord
import ReflexiveArchitecture.Instances.ConcreteFromNEMS

namespace AdequacyArchitecture.Instances

open ReflexiveArchitecture
open ReflexiveArchitecture.Instances
open NemS
open NemS.Physical

/-- Definitional expansion: faithful outer = `concreteNEMSReflexiveLayer` at **`haltingFramework`**. -/
theorem faithfulNEMSHaltingReflexiveLayer_eq_concrete_halting :
    faithfulNEMSHaltingReflexiveLayer =
      concreteNEMSReflexiveLayer haltingFramework (dc := haltingFramework_diagonalCapable) :=
  rfl

/-- `nemsSemanticPairI0` **is** `haltingFramework` (left witness of the Level 3b row). -/
theorem nems_semantic_pair_i0_eq_halting : nemsSemanticPairI0 = haltingFramework :=
  rfl

/-- Same EPIC_018 outer package, phrased at the Level 3b **left** grid point. -/
theorem faithfulNEMSHaltingReflexiveLayer_eq_concrete_at_semantic_pair_left :
    faithfulNEMSHaltingReflexiveLayer =
      concreteNEMSReflexiveLayer nemsSemanticPairI0 (dc := haltingFramework_diagonalCapable) :=
  rfl

/-- The Level 3b **right** grid (`Fin 2` halting-code slice) is not the halting `ℕ` grid. -/
theorem nems_semantic_pair_i1_ne_halting : nemsSemanticPairI1 ≠ haltingFramework :=
  Ne.symm haltingFramework_ne_fin2HaltingCodeFramework

/-- Corollary: the reflexive outer layer is **not** silently parameterized by `fin2HaltingCodeFramework` in
`NEMSFaithful`—that file fixes `haltingFramework` only (`faithfulNEMSHaltingReflexiveLayer_eq_concrete_halting`). -/
theorem nems_semantic_pair_i1_ne_semantic_pair_i0 : nemsSemanticPairI1 ≠ nemsSemanticPairI0 :=
  nems_framework_semantic_pair_points_ne.symm

end AdequacyArchitecture.Instances
