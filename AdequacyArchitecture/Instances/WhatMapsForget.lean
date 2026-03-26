/-
  Strata — geometry of what maps forget (`UniversalForgetting`, fundamental residual package).

  Imports the spine via `AdequacyArchitecture.Residual.Strata` (SPEC_001 names).
-/

import AdequacyArchitecture.Residual.Strata

universe u

namespace AdequacyArchitecture.Instances

open ReflexiveArchitecture.Universal.Residual

/-- Every function `π : E → B` yields Strata's `FundamentalResidualPackage` on `rcsOfMap π`. -/
theorem every_map_has_fundamental_residual_package (E B : Type u) (π : E → B) :
    Nonempty (FundamentalResidualPackage (rcsOfMap π)) :=
  fundamental_package_exists (rcsOfMap π)

end AdequacyArchitecture.Instances
