/-
  NEMS instance band — Strata packages the outer layer as `nemsReflexiveLayer`
  (`ReflexiveArchitecture.Instances.FromNEMS`), pulled in transitively via
  `lakefile` `require «reflexive-architecture»`.

  **Shared `Fin 2` corpus track:** `Instances/CorpusDischarge.lean` (`nemsCorpusReflexiveLayer`) — **SPEC_013**. **Faithful halting discharge:** `Instances/NEMSFaithful.lean` (`concreteNEMSReflexiveLayer` on `NemS.Physical.haltingFramework`). **TODO:** additional `Framework` + barrier packaging beyond halting (`nems-lean`, SPEC_001).
-/

import AdequacyArchitecture.Core.Basic
import ReflexiveArchitecture.Instances.FromNEMS

universe u

namespace AdequacyArchitecture.Instances

open ReflexiveArchitecture

/-- Trivial outer layer: no internal theories; `BarrierHyp` false so the barrier is vacuous. -/
@[reducible]
def trivialReflexiveLayer : Outer.ReflexiveLayer Unit where
  Theory := Unit
  InternalTheory := fun _ => False
  TotalOn := fun _ => False
  SemanticRemainder := fun _ => True
  FinalSelfTheory := fun _ => False
  BarrierHyp := False
  no_final_self_theory := fun h => False.elim h
  no_remainder_and_total_implies_final := fun _ hT => False.elim hT

theorem nonempty_nems_outer_layer : Nonempty (Outer.ReflexiveLayer Unit) :=
  ⟨trivialReflexiveLayer⟩

/-- Strata outer layer is nonempty (witness `Unit`). -/
def NEMSInstancePlaceholder : Prop := Nonempty (Outer.ReflexiveLayer Unit)

theorem nems_instance_placeholder_holds : NEMSInstancePlaceholder :=
  nonempty_nems_outer_layer

end AdequacyArchitecture.Instances
