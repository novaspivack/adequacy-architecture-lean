/-
  Stratified slice of the lawful universality class 𝒞 (SPEC_009).

  **Outer layer:** `LawfulAdequacyArchitecture` (SPEC_008).
  **First inner anti-vacuity:** burden is not universally realized at some mode — same mode,
  two accounts differ on `B.burden m`.

  Middle (gluing) / deeper inner (residual) interfaces are specified in SPEC_009 and wired
  through existing Residual / LocalGlobal bands — not `Prop := True` placeholders here.
-/

import AdequacyArchitecture.Core.Basic
import AdequacyArchitecture.Lawful.LawfulStructures

universe u

namespace AdequacyArchitecture.Lawful

variable {α : Type u}

/-- Stratified lawful adequacy architecture: outer lawful spine + burden variation witness.

Burden **variation** rules out the degenerate case “`B.burden m` holds for every account”
at some mode, which would make carrier witnesses collapse to vacuity.

**Σ' data** (not mere `∃`) so bottleneck bundles and sigma corollaries extract without choice. -/
structure StratifiedLawfulAdequacyArchitecture (α : Type u) where
  outer : LawfulAdequacyArchitecture α
  burden_variation :
    Σ' (m : BurdenMode), Σ' (A : Account α), Σ' (A' : Account α), outer.B.burden m A ∧ ¬ outer.B.burden m A'

end AdequacyArchitecture.Lawful
