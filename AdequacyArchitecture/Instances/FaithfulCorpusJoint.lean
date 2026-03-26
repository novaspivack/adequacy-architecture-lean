/-
  Joint **faithful** NEMS + IC facts on the **halting framework** and **NEMS spine** — re-exported
  from `ReflexiveArchitecture.Bridge.DirectCrossCorpusBridge` (`nems_spine_strata_from_sources`,
  `nems_spine_both_strata`).

  Packaging the conjunction **inside** this repo with `∧` or a custom `structure` hits unsolved
  universe metavariables (polymorphic `Outer.ReflexiveLayer` vs `Inner.CertificationLayer`). The
  Strata bridge theorems are the canonical machine-checked joint witness.

  **Note:** `nems_spine_strata_from_sources` uses `haltingFrameworkDC` from the bridge file; Adequacy
  `NEMSFaithful.lean` uses `haltingFramework_diagonalCapable` from `NemS.Physical` — both discharge
  `SemanticRemainder` via `diagonal_barrier_rt` on the same `haltingFramework`.

  **Projection in Adequacy:** `HonestyBridge.lean` names the two conjuncts as separate theorems
  (`faithful_joint_strata_outer_semantic_remainder`, `faithful_joint_strata_inner_enriched_irreducibility`)
  without using `.1`/`.2` on the joint statement (universe-polymorphism pitfall).
-/

import ReflexiveArchitecture.Bridge.DirectCrossCorpusBridge

namespace AdequacyArchitecture.Instances

open ReflexiveArchitecture.Bridge

/-- Same as Strata `nems_spine_strata_from_sources` — joint `ConcreteFrom*` witness (NEMS outer + IC inner on spine). -/
abbrev faithful_joint_strata_from_sources := nems_spine_strata_from_sources

/-- Same as Strata `nems_spine_both_strata` — abstract joint statement (barrier RT + T-C+.6-style pair). -/
abbrev faithful_joint_both_strata := nems_spine_both_strata

end AdequacyArchitecture.Instances
