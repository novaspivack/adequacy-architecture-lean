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
  Strata (`reflexive-architecture-lean`): same Mathlib pin; transitively depends on
  `nems-lean` and `infinity-compression-lean` as declared in that package’s lakefile.
-/
require «reflexive-architecture» from git
  "https://github.com/novaspivack/reflexive-architecture-lean.git" @ "50a28eb26eb4f4d917d194a9b2e7ccc3764f0787"

/-
  APS recursion uniformization (`aps-recursion-uniformization-lean`): `IndexedAPS`, **interpolation exactness**
  `HasICompIndexed ↔ HasFiniteTracking ∧ HasGluing` (`APSUniformization.Synthesis.aps_interpolation_exactness`),
  and `corrected_exactness_iff` (`APSRecComp`).
-/
require aps_recursion_uniformization_lean from git
  "https://github.com/novaspivack/aps-recursion-uniformization-lean.git" @ "b96ab3631081364074aa87d588735e60a35ee2ea"

@[default_target]
lean_lib «AdequacyArchitecture» where
  roots := #[`AdequacyArchitecture]
