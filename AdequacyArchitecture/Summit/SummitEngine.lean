/-
  SPEC_020_LG4 — **Summit engine (residual + local–global):** single hub re-proving
  Strata residual packages (`WhatMapsForget`) and middle-layer composition from
  tracking + gluing (`LocalGlobal`) under advisor-facing names.

  No new mathematical content beyond the two referenced theorems.
-/

import AdequacyArchitecture.LocalGlobal.GluingObstruction
import AdequacyArchitecture.Instances.WhatMapsForget

namespace AdequacyArchitecture.Summit

universe u

open AdequacyArchitecture.LocalGlobal
open AdequacyArchitecture.Instances
open ReflexiveArchitecture
open ReflexiveArchitecture.Universal.Residual

/-- Engine: finite tracking + gluing ⇒ indexed composition (`SPEC_020`). -/
theorem summit_engine_composition_from_gluing {S : Type u} [M : Middle.RealizationLayer S]
    (h : M.HasFiniteTracking ∧ M.HasGluing) : M.ICompIdx :=
  composition_from_tracking_and_gluing h

/-- Engine: every `π : E → B` yields `FundamentalResidualPackage` on `rcsOfMap π` (`SPEC_020`). -/
theorem summit_engine_fundamental_residual (E B : Type u) (π : E → B) :
    Nonempty (FundamentalResidualPackage (rcsOfMap π)) :=
  every_map_has_fundamental_residual_package E B π

end AdequacyArchitecture.Summit
