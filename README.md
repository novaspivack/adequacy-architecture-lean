# adequacy-architecture-lean


## Research Program

This repository is part of the **Reflexive Reality** research program by [Nova Spivack](https://www.novaspivack.com/).

**What this formalizes:** Adequacy Architecture (§B5f): unified gate theorem — heterogeneous outer certificate forms collapse; strict three-level architecture.

| Link | Description |
|------|-------------|
| [Research page](https://www.novaspivack.com/research/) | Full index of all papers, programs, and Lean archives |
| [Full abstracts](https://novaspivack.github.io/research/abstracts/#b5f-adequacy-architecture) | Complete abstract for this library's papers |
| [Zenodo program hub](https://doi.org/10.5281/zenodo.19429270) | Citable DOI hub for the NEMS program |

All results are machine-checked in Lean 4 with a zero-sorry policy on proof targets.
See [MANIFEST.md](MANIFEST.md) for the sorry audit (if present).

---

Lean 4 + Mathlib library for the **Adequacy Architecture** program — outer admissibility, unified certificate-world structure, and the three-level architecture theorem.

## What it proves

Heterogeneous outer certificate forms (compressed witnesses, abstraction layers, quotient representations, transport claims, upgrade witnesses) collapse to one unified admissibility gate in a disciplined certificate world. Above the gate, a richer second layer is canonically forced without new hypotheses. Stronger branch content sits above both as a partially reconstructible but irreducibly richer residual band. The strict three-level architecture is witnessed by named, machine-checked theorems.

## Build

```bash
lake update
lake exe cache get   # pre-built Mathlib .olean files (strongly recommended)
lake build
```

**Toolchain:** `lean-toolchain` must match the Mathlib pin in `lakefile.lean`.

## Root import

`AdequacyArchitecture.lean` imports the full module surface.

## Documentation

- **[MANIFEST.md](MANIFEST.md)** — module layout, entry-point names, last verified build
- **[ARTIFACT.md](ARTIFACT.md)** — what the library proves, proof policy, reproduction steps
- **[THEOREM_INVENTORY.md](THEOREM_INVENTORY.md)** — sequenced spine of named definitions and theorems

The companion papers are published on Zenodo — see [novaspivack.com/research](https://www.novaspivack.com/research).
<!-- NOVA_ZPO_ZENODO_SOFTWARE_BEGIN -->
**Archival software (Zenodo):** https://doi.org/10.5281/zenodo.19429258
<!-- NOVA_ZPO_ZENODO_SOFTWARE_END -->
