# Adequacy Architecture — theorem inventory (Lean names)

**Last updated:** 2026-03-24  
**Purpose:** Single **sequenced** index of **named** `def`s / `theorem`s with **`AdequacyArchitecture/...` paths** for drafting papers and cross-walking specs. Not every helper lemma is listed; this is the **spine**.

**Build:** `adequacy-architecture-lean/` — root import `AdequacyArchitecture.lean`.

**Completeness:** This file is **spine-complete** for whatever is **named and exported** in the library. For every `theorem`/`def` in a module, also use `MANIFEST.md`, `ADEQUACY_FORMALIZATION_MAP.md`, and search inside `AdequacyArchitecture/`.

**Paper prep mirror:** `specs/NOTES/ADEQUACY_THEOREM_INVENTORY_LEAN_PAPER_PREP.md` (symlink to this file).

---

## Meta (scaffold)

| Module | Covered in inventory section |
|--------|------------------------------|
| `AdequacyArchitecture/Basic.lean` | Scaffold |

---

## Program scaffold (v0)

| Kind | Lean name | Module |
|------|-----------|--------|
| def | `basicAnchor` | `AdequacyArchitecture/Basic.lean` |
| def | `programRoot` | `AdequacyArchitecture.lean` (root namespace) |

---

## Reserved EPIC sections

Add rows below as epics land (mirror `specs/IN-PROCESS/` and `specs/COMPLETE/`). Example:

| Kind | Lean name | Module |
|------|-----------|--------|
| theorem | `…` | `AdequacyArchitecture/…` |

---

## Changelog

| Date | Change |
|------|--------|
| 2026-03-24 | Initial inventory alongside scaffold (`Basic` + root). |
