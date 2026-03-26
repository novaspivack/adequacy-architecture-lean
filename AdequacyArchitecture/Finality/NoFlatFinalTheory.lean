/-
  G2 — No “flat” final self-theory: no theory is simultaneously final-self and internal under the barrier.
-/

import AdequacyArchitecture.Core.Basic
import ReflexiveArchitecture.Outer.Interface

universe u

namespace AdequacyArchitecture.Finality

open ReflexiveArchitecture

def NoFlatFinalTheoryWeak (S : Type u) [M : Outer.ReflexiveLayer S] : Prop :=
  ∀ T : M.Theory, ¬ M.FinalSelfTheory T

end AdequacyArchitecture.Finality
