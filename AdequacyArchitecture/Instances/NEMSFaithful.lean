/-
  Faithful NEMS outer layer on the **halting framework** (`NemS.Physical.Instantiation`).

  `ReflexiveArchitecture.Instances.concreteNEMSReflexiveLayer` packages `NemS.MFRR.diagonal_barrier_rt`
  into `Outer.ReflexiveLayer Framework` (EPIC_018 in Strata). `DiagonalCapable` is passed explicitly
  via `haltingFramework_diagonalCapable`.

  The `Fin 2` corpus corridor (`CorpusDischarge.lean`) stays the toy alignment; this module is the
  **NEMS-native** Strata index (`Framework`).   SPEC_024 **Level 3** bridge rows on this carrier live in `NEMSFrameworkBridgeRecord.lean`; EPIC_018
  **parameter bookkeeping** vs Level 3b witnesses lives in `NEMSBridgeReflexiveAnchor.lean`. Levels 1–2 on the
  corridor in `NEMSBridgeCoreRecord.lean`.
-/

import ReflexiveArchitecture.Instances.ConcreteFromNEMS
import NemS.Physical.Instantiation

namespace AdequacyArchitecture.Instances

open ReflexiveArchitecture
open ReflexiveArchitecture.Instances
open NemS
open NemS.Framework
open NemS.MFRR
open NemS.Physical

@[reducible]
noncomputable def faithfulNEMSHaltingReflexiveLayer : Outer.ReflexiveLayer Framework :=
  concreteNEMSReflexiveLayer haltingFramework (dc := haltingFramework_diagonalCapable)

theorem nonempty_faithful_nems_halting_outer_layer : Nonempty (Outer.ReflexiveLayer Framework) :=
  ⟨faithfulNEMSHaltingReflexiveLayer⟩

theorem faithful_nems_barrier_holds : faithfulNEMSHaltingReflexiveLayer.BarrierHyp :=
  trivial

theorem faithful_nems_semantic_remainder_at_unit :
    faithfulNEMSHaltingReflexiveLayer.SemanticRemainder PUnit.unit :=
  diagonal_barrier_rt haltingFramework (dc := haltingFramework_diagonalCapable)

end AdequacyArchitecture.Instances
