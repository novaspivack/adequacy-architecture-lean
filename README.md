# adequacy-architecture-lean

Lean 4 + **Mathlib** for the **Adequacy Architecture** program. Layout matches `reflexive-architecture-lean`: `lakefile.lean`, `AdequacyArchitecture.lean`, `AdequacyArchitecture/`.

**You need Mathlib, but you should not compile Mathlib from source** on your machine. After `lake update`, always run **`lake exe cache get`** to download pre-built artifacts, then `lake build`. See **`../docs/optional_mathlib.md`**.

## Build

```bash
lake update
lake exe cache get
lake build
```

**Toolchain:** `lean-toolchain` must match the Mathlib pin in `lakefile.lean`.

## Root import

`AdequacyArchitecture.lean` imports the initial module surface (`Basic`).

## Papers

See `paper/build_papers.sh` and `paper/Program_Notes.tex` (placeholder).

## Manifest, artifact, inventory

- **`MANIFEST.md`** — module layout, entry-point names, last verified build.  
- **`ARTIFACT.md`** — what the library proves, proof policy, reproduction.  
- **`THEOREM_INVENTORY.md`** — sequenced spine of named defs/theorems (paper/spec crosswalk).  
- Paper-prep mirror: `specs/NOTES/ADEQUACY_THEOREM_INVENTORY_LEAN_PAPER_PREP.md` → same file.
<!-- NOVA_ZPO_ZENODO_SOFTWARE_BEGIN -->
**Archival software (Zenodo):** https://doi.org/10.5281/zenodo.19429258
<!-- NOVA_ZPO_ZENODO_SOFTWARE_END -->
