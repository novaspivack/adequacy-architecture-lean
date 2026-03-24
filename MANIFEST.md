# adequacy-architecture-lean — manifest

**Toolchain:** `leanprover/lean4:v4.29.0-rc6`  
**Mathlib:** v4.29.0-rc6 (via `lakefile.lean`); use **`lake exe cache get`** after `lake update` (pre-built artifacts — do not compile Mathlib from source)  
**Build:** `lake build` from this directory  
**Root import:** `AdequacyArchitecture.lean`  
**Formalization map:** `ADEQUACY_FORMALIZATION_MAP.md` (module tree + theorem glosses)  
**Theorem inventory:** `THEOREM_INVENTORY.md` (sequenced Lean names for paper/spec crosswalk)  
**Last verified:** 2026-03-24 — clean build on rc6; scaffold only — expand counts as formalization grows.  
**Lake deps:** none beyond Mathlib; **`lake exe cache get`** fetches pre-built Mathlib — see `docs/optional_mathlib.md`.

---

## Layout

| Area | Path | Role |
|------|------|------|
| Core | `AdequacyArchitecture/Basic.lean` | Initial module anchor |

Add subfolders under `AdequacyArchitecture/` as the program grows. Update **`THEOREM_INVENTORY.md`** when you add named entry points.

---

## Entry-point theorems

### Scaffold (v0)

| Name | File |
|------|------|
| `AdequacyArchitecture.basicAnchor` | `AdequacyArchitecture/Basic.lean` |
| `AdequacyArchitecture.programRoot` | `AdequacyArchitecture.lean` |

---

## See also

- **`ARTIFACT.md`** — build status, proof policy, reproduction.  
- **`THEOREM_INVENTORY.md`** — full spine table (by EPIC as the program grows).  
- **`ADEQUACY_FORMALIZATION_MAP.md`** — informal module roles and boundaries.
