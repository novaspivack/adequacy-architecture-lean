/-
  Master theorems over `LawfulAdequacyArchitecture` (SPEC_008 Phase D).

  Summit shape S1 becomes a **theorem** for members of 𝒞, not a conjecture over raw `P,B`.
-/

import AdequacyArchitecture.Lawful.LawfulStructures
import AdequacyArchitecture.Summit.UniversalIrreducibleAdequacy

universe u

namespace AdequacyArchitecture.Lawful

open AdequacyArchitecture.Burden
open AdequacyArchitecture.Summit

variable {α : Type u}

/-- **Master irreducible burden** (B1 at each mode, packaged by `LawfulAdequacyArchitecture`). -/
theorem master_irreducible_burden (𝔸 : LawfulAdequacyArchitecture α) (m : AdeqMode) (A : Account α)
    (hA : 𝔸.P.adeq m A) : ∃ m' : BurdenMode, 𝔸.B.burden m' A :=
  irreducible_burden_of_adequacy 𝔸.P 𝔸.B m A (𝔸.forces_each m) hA

/-- **Summit S1** as a theorem for any **lawful** architecture: same shape as `UniversalIrreducibleAdequacyConjecture`. -/
theorem universal_irreducible_adequacy_lawful (𝔸 : LawfulAdequacyArchitecture α) :
    UniversalIrreducibleAdequacyConjecture α 𝔸.P 𝔸.B := fun m A hA =>
  master_irreducible_burden 𝔸 m A hA

end AdequacyArchitecture.Lawful
