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
require «reflexive-architecture» from git
  "https://github.com/novaspivack/reflexive-architecture-lean.git" @ "1dc9b05915832f88d378bd7813db9e43dab2c019"

/-
  APS recursion uniformization (`aps-recursion-program`): `IndexedAPS`, **interpolation exactness**
  `HasICompIndexed ↔ HasFiniteTracking ∧ HasGluing` (`APSUniformization.Synthesis.aps_interpolation_exactness`),
  and `corrected_exactness_iff` (`APSRecComp`).
-/
require aps_recursion_uniformization_lean from git
  "https://github.com/novaspivack/aps-recursion-uniformization-lean.git" @ "f5566e70b56a8c5b087625219379bd23c3ca517d"

@[default_target]
lean_lib «AdequacyArchitecture» where
  roots := #[`AdequacyArchitecture]
