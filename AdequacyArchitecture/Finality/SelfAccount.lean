/-
  G1 — Self-adequacy burden: Strata outer layer `BarrierHyp` (diagonal / semantic remainder pattern).
-/

import AdequacyArchitecture.Core.Basic
import ReflexiveArchitecture.Outer.Interface

universe u

namespace AdequacyArchitecture.Finality

open ReflexiveArchitecture

def SelfAdequacyBurden (S : Type u) [M : Outer.ReflexiveLayer S] : Prop :=
  M.BarrierHyp

end AdequacyArchitecture.Finality
