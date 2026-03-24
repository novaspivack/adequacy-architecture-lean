/-
  Route architecture features (split, refinement, fiber, gluing, …).
-/

import AdequacyArchitecture.Core.Basic

universe u

namespace AdequacyArchitecture.Route

structure RouteArchitectureClass ( _α : Type u) where
  hasSplit : Prop
  hasRefinement : Prop

end AdequacyArchitecture.Route
