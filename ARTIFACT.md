# adequacy-architecture-lean — artifact documentation

**Version:** v0.2.0  
**Lean:** leanprover/lean4:v4.29.0-rc6  
**Mathlib:** v4.29.0-rc6 — use **`lake exe cache get`**  
**Build:** `lake build` — **0 sorry** in proof terms; **0** custom program axioms  
**Lake deps:** Mathlib only — see `docs/optional_mathlib.md`  
**Workspace handoff:** `../specs/IN-PROCESS/MASTER_STATUS_AND_HANDOFF.md`

---

## What this artifact proves

**Phase 1 (A1–B3):** Machine-checked **Core**, **Foundation**, and **Burden** bands: typed adequacy modes, burden predicates, **strong** `no_free_adequate_collapse` (from `∀ A', Adeq → ∃ burden`), internality barrier **modulo explicit hypothesis**, and relocation lemmas.

**Toy model:** `Toy/Fin2Model.lean` — **`Fin 2`** account distinguishing both points; **proved** `toy_adequacy_forces_burden` and **proved** inadequacy after **constant collapse** (`toy_not_adequate_after_constant_collapse`).

**Upper bands (C–G, Summit, Instances):** **structures and named obligations** compile; **not** claimed proved except where noted in `MANIFEST.md`. Summit **conjectures** are **strong `def` statements** (open).

---

## Proof status

**Zero sorry.** **Zero** smuggled conclusions: `AdequacyForcesSomeBurden` is **hypothesis** for abstract B1; **constructed** in `Fin 2` toy.

---

## Reproduction

```bash
cd adequacy-architecture-lean
lake update
lake exe cache get
lake build
```

---

## Key theorem summary

See **[THEOREM_INVENTORY.md](THEOREM_INVENTORY.md)** and **[MANIFEST.md](MANIFEST.md)**.
