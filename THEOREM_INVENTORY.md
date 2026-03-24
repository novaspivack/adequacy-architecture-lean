# Adequacy Architecture — theorem inventory (Lean names)

**Last updated:** 2026-03-24  
**Purpose:** Sequenced index of named `def`s / `theorem`s. **Paper prep mirror:** `specs/NOTES/ADEQUACY_THEOREM_INVENTORY_LEAN_PAPER_PREP.md`.

---

## Meta

| Module | Coverage |
|--------|----------|
| `Core/*` | Ontology: modes, `AdequacyPredicates`, `BurdenPredicates`, `RouteDatum`, collapse, transform |
| `Foundation/*` | A1–A4 |
| `Burden/*` | B1–B3 |
| `Toy/Fin2Model` | Earned `Fin 2` model |
| `Residual/*` … `Instances/*` | Scaffolds + TODO imports |

---

## Foundation (A1–A4)

| Kind | Lean name | Module |
|------|-----------|--------|
| def | `trivialInterface` | `Foundation/AdequacyInterface.lean` |
| theorem | `adequacy_interface_exists` | same |
| def | `InterfaceNondegenerate` | same |
| def | `AdequacyModesComparable` | same |
| theorem | `modes_comparable_of_trivial` | same |
| theorem | `carrier_exists_of_adequacy_mode` | `Foundation/BurdenCarrierExistence.lean` |
| def | `burdenModeOfAdeq` | same |
| theorem | `burden_mode_has_admissible_carrier` | same |
| theorem | `internality_outsourcing_barrier` | `Foundation/InternalityOutsourcing.lean` |
| theorem | `hidden_distinction_is_burden` | `Foundation/NoFreeDeterminacy.lean` |
| theorem | `no_free_determinacy` | same |

## Burden (B1–B3)

| Kind | Lean name | Module |
|------|-----------|--------|
| def | `AdequacyForcesSomeBurden` | `Burden/IrreducibleAdequacy.lean` |
| theorem | `irreducible_burden_of_adequacy` | same |
| theorem | `irreducible_burden_of_adequacy_rich` | same |
| theorem | `no_free_adequate_collapse` | `Burden/NoFreeCollapse.lean` |
| abbrev | `no_free_adequate_collapse_weak` | same |
| theorem | `removes_all_burden_implies_inadequate` | same |
| theorem | `burden_not_erased_only_relocated` | `Burden/Relocation.lean` |
| theorem | `adequacy_preserving_drop_implies_relocation` | same |
| def | `RelocationPair` | `Burden/RelocationClass.lean` |

## Toy (`Fin 2`)

| Kind | Lean name | Module |
|------|-----------|--------|
| def | `distinguishingAccount` | `Toy/Fin2Model.lean` |
| def | `toyPred`, `toyBurden` | same |
| theorem | `toy_adequacy_forces_burden` | same |
| theorem | `toy_B1` | same |
| def | `constantCollapse` | same |
| theorem | `constant_removes_all_burden` | same |
| theorem | `toy_not_adequate_after_constant_collapse` | same |

## Summit (statements — not proved)

| Kind | Lean name | Module |
|------|-----------|--------|
| def | `UniversalIrreducibleAdequacyConjecture` | `Summit/UniversalIrreducibleAdequacy.lean` |
| def | `UniversalBurdenRelocationConjecture` | `Summit/UniversalBurdenRelocation.lean` |

---

## Changelog

| Date | Change |
|------|--------|
| 2026-03-24 | Full program scaffold + Phase 1 proofs + `Fin 2` model; epics SPEC_001–007 completed in specs. |
