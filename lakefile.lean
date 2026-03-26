import Lake
open Lake DSL

package «adequacy-architecture» where
  leanOptions := #[⟨`autoImplicit, false⟩]

/-
  Mathlib is a **dependency** of this project. You should **not** compile all of
  Mathlib from source locally: after `lake update`, run **`lake exe cache get`**
  to download **pre-built** `.olean` artifacts into `~/.cache/mathlib/`, then
  `lake build` only compiles this repo’s files. See `docs/optional_mathlib.md`.
-/

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0-rc6"

/-
  Strata (`reflexive-architecture-lean`): same Mathlib pin; pulls in `nems-lean` +
  `infinity-compression-lean` via *its* lakefile (paths relative to that repo:
  `../../nems-lean`, `../../infinity-compression/infinity-compression-lean`).
-/
require «reflexive-architecture» from "../../reflexive-architecture/reflexive-architecture-lean"

/-
  APS recursion uniformization (`aps-recursion-program`): `IndexedAPS`, **interpolation exactness**
  `HasICompIndexed ↔ HasFiniteTracking ∧ HasGluing` (`APSUniformization.Synthesis.aps_interpolation_exactness`),
  and `corrected_exactness_iff` (`APSRecComp`). Sibling path from this package directory.
-/
require aps_recursion_uniformization_lean from "../../aps-recursion-program/aps-recursion-uniformization-lean"

@[default_target]
lean_lib «AdequacyArchitecture» where
  roots := #[`AdequacyArchitecture]
