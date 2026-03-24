# adequacy-architecture-lean — artifact documentation

**Version:** v0.1.0 (scaffold)  
**Lean:** leanprover/lean4:v4.29.0-rc6  
**Mathlib:** v4.29.0-rc6 (pinned in `lakefile.lean`); use **`lake exe cache get`** so local builds use **pre-built** Mathlib artifacts, not a source compile  
**Build:** see `lake build` output; **0 sorry** in shipped proof terms; **0 custom axioms** beyond Mathlib  
**Lake deps:** Mathlib only — see `docs/optional_mathlib.md`  
**Commit:** `(see git log)` — see `MANIFEST.md` for the theorem index, `THEOREM_INVENTORY.md` for the sequenced spine, and `ADEQUACY_FORMALIZATION_MAP.md` for module glosses.

---

## What this artifact proves

This Lean 4 library is the **machine-checked home** of the **Adequacy Architecture** program. The current tree is a **scaffold**: root import `AdequacyArchitecture.lean`, initial module `AdequacyArchitecture/Basic.lean`, and placeholders `basicAnchor` / `programRoot` so `lake build` and CI have a stable target.

As you add epics, extend this section with the same level of detail as `reflexive-architecture-lean/ARTIFACT.md` (milestones, proof obligations, and honest scope notes).

---

## Proof status

**Zero sorry** in shipped proof terms. **Zero** program-specific axioms beyond Mathlib.

---

## Reproduction

```bash
cd adequacy-architecture-lean
lake update
lake exe cache get
lake build
```

Verified clean on `leanprover/lean4:v4.29.0-rc6` with Mathlib `v4.29.0-rc6` via **cached** artifacts (`docs/optional_mathlib.md`).

---

## Key theorem summary

| Theorem / def | Location | Status |
|---------------|----------|--------|
| `basicAnchor` | `AdequacyArchitecture/Basic.lean` | ✓ scaffold |
| `programRoot` | `AdequacyArchitecture.lean` | ✓ scaffold |

For the full sequenced list see **[THEOREM_INVENTORY.md](THEOREM_INVENTORY.md)**.  
For the full manifest table (entry points and future milestones) see **[MANIFEST.md](MANIFEST.md)**.
