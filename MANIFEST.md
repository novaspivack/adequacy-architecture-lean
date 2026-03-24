# adequacy-architecture-lean — manifest

**Toolchain:** `leanprover/lean4:v4.29.0-rc6`  
**Mathlib:** v4.29.0-rc6 (via `lakefile.lean`); use `lake exe cache get`  
**Build:** `lake build` from this directory  
**Root import:** `AdequacyArchitecture.lean`  
**Formalization map:** `ADEQUACY_FORMALIZATION_MAP.md`  
**Theorem inventory:** `THEOREM_INVENTORY.md`  
**Last verified:** 2026-03-24 — clean build; Phase 1 (A–B) **proved** without `sorry`; upper bands **scaffolded**; `Fin 2` toy model **proved**.  
**Lake deps:** Mathlib only.

---

## Layout

| Area | Path | Role |
|------|------|------|
| Core | `AdequacyArchitecture/Core/` | Modes, `RichTarget`, accounts, adequacy/burden preds, carriers, transform, collapse, `RouteDatum` |
| Foundation | `AdequacyArchitecture/Foundation/` | A1–A4 |
| Burden | `AdequacyArchitecture/Burden/` | B1–B3 |
| Toy | `AdequacyArchitecture/Toy/Fin2Model.lean` | Earned `Fin 2` model |
| Residual | `AdequacyArchitecture/Residual/` | C1–C4 scaffold + joint observability |
| Local/global | `AdequacyArchitecture/LocalGlobal/` | D1–D2 scaffold |
| Dynamics | `AdequacyArchitecture/Dynamics/` | E1–E2 scaffold |
| Adjudication | `AdequacyArchitecture/Adjudication/` | E3–E4 scaffold |
| Route | `AdequacyArchitecture/Route/` | F1–F2 scaffold (`Route/` band; `RouteDatum` in Core) |
| Finality | `AdequacyArchitecture/Finality/` | G1–G2 scaffold |
| Summit | `AdequacyArchitecture/Summit/` | S1–S2 **conjecture statements** (open) |
| Instances | `AdequacyArchitecture/Instances/` | NEMS, APS, IC, WhatMapsForget — TODO `require` Strata/IC |

---

## Entry-point theorems (Phase 1)

| Name | File |
|------|------|
| `AdequacyArchitecture.Foundation.adequacy_interface_exists` | `Foundation/AdequacyInterface.lean` |
| `AdequacyArchitecture.Foundation.carrier_exists_of_adequacy_mode` | `Foundation/BurdenCarrierExistence.lean` |
| `AdequacyArchitecture.Foundation.internality_outsourcing_barrier` | `Foundation/InternalityOutsourcing.lean` |
| `AdequacyArchitecture.Burden.no_free_adequate_collapse` | `Burden/NoFreeCollapse.lean` |
| `AdequacyArchitecture.Toy.toy_not_adequate_after_constant_collapse` | `Toy/Fin2Model.lean` |

---

## See also

- **`ARTIFACT.md`** — proof policy, reproduction.  
- **`specs/IN-PROCESS/MASTER_STATUS_AND_HANDOFF.md`** — program handoff (workspace).  
- **`specs/COMPLETE/`** — completed epic specs SPEC_001–007.
