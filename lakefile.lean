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

/-
  Strata (`reflexive-architecture-lean`): same Mathlib pin; transitively depends on
  `nems-lean` and `infinity-compression-lean` as declared in that package’s lakefile.
-/
require «reflexive-architecture» from git
  "https://github.com/novaspivack/reflexive-architecture-lean.git" @ "main"

/-
  APS recursion uniformization (`aps-recursion-uniformization-lean`): `IndexedAPS`, **interpolation exactness**
  `HasICompIndexed ↔ HasFiniteTracking ∧ HasGluing` (`APSUniformization.Synthesis.aps_interpolation_exactness`),
  and `corrected_exactness_iff` (`APSRecComp`).
-/
require aps_recursion_uniformization_lean from git
  "https://github.com/novaspivack/aps-recursion-uniformization-lean.git" @ "main"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.1"

@[default_target]
lean_lib «AdequacyArchitecture» where
  roots := #[`AdequacyArchitecture]
