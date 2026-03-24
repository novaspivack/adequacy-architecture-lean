# Adequacy formalization map

**Purpose:** Module roles; pair with `MANIFEST.md` and `THEOREM_INVENTORY.md`.

**Program handoff:** `../specs/IN-PROCESS/MASTER_STATUS_AND_HANDOFF.md`

---

## Module tree

| Path | Role |
|------|------|
| `AdequacyArchitecture/Core/*` | Ontology: `AdeqMode`, `BurdenMode`, `CarrierTag`, `RichTarget`, `Account`, predicates, `RouteDatum` (renamed from `Route` to avoid clashing with `Route/` band) |
| `AdequacyArchitecture/Foundation/*` | A1–A4 |
| `AdequacyArchitecture/Burden/*` | B1–B3 + `RelocationPair` |
| `AdequacyArchitecture/Toy/Fin2Model.lean` | `Fin 2` distinguishing account; collapse kills adequacy |
| `AdequacyArchitecture/Residual/*` | C-track scaffold — **next:** import Strata `Universal/Residual/*` |
| `AdequacyArchitecture/LocalGlobal/*` | D-track scaffold |
| `AdequacyArchitecture/Dynamics/*` | E1–E2 scaffold |
| `AdequacyArchitecture/Adjudication/*` | E3–E4 scaffold |
| `AdequacyArchitecture/Route/*` | F-track scaffold |
| `AdequacyArchitecture/Finality/*` | G-track scaffold |
| `AdequacyArchitecture/Summit/*` | S1–S2 conjecture `def`s (open) |
| `AdequacyArchitecture/Instances/*` | External corpus hooks — TODO `lakefile` `require` |

---

## Strata alignment (names only — see SPEC_001 in `specs/COMPLETE/`)

When wiring imports: `layered_architecture_theorem`, `vanishingCriterion`, `rcsOfMap`, etc. — **never rename**; copy from Strata `MANIFEST.md`.
