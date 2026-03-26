/-
  G2 — Counterfeit simplicity: existence of an internal theory candidate (outer-layer predicate).
-/

import AdequacyArchitecture.Core.Basic
import ReflexiveArchitecture.Outer.Interface

universe u

namespace AdequacyArchitecture.Finality

open ReflexiveArchitecture

def NoCounterfeitSimplicity (S : Type u) [M : Outer.ReflexiveLayer S] : Prop :=
  ∃ T : M.Theory, M.InternalTheory T

end AdequacyArchitecture.Finality
