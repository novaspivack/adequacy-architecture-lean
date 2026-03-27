# adequacy-architecture-lean — artifact documentation

**Version:** v0.2.0  
**Lean:** leanprover/lean4:v4.29.0-rc6  
**Mathlib:** v4.29.0-rc6 — use **`lake exe cache get`**  
**Build:** `lake build` — **0 sorry** in proof terms; **0** custom program axioms  
**Lake deps:** Mathlib + **`reflexive-architecture`** + **`aps_recursion_uniformization_lean`** (`lakefile.lean`); **NEMS** / **infinity-compression** arrive **transitively** through **`reflexive-architecture`**. Not Mathlib-only.  
**Workspace handoff:** `../specs/IN-PROCESS/STATUS_AND_HANDOFF.md` (canonical advisor brief). **Legacy filename:** `../specs/IN-PROCESS/MASTER_STATUS_AND_HANDOFF.md` redirects to the same document.

---

## What this artifact proves

**Phase 1 (A1–B3):** Machine-checked **Core**, **Foundation**, and **Burden** bands: typed adequacy modes, burden predicates, **strong** `no_free_adequate_collapse` (from `∀ A', Adeq → ∃ burden`), internality barrier **modulo explicit hypothesis**, and relocation lemmas.

**Toy model:** `Toy/Fin2Model.lean` — **`Fin 2`** account distinguishing both points; **proved** `toy_adequacy_forces_burden` and **proved** inadequacy after **constant collapse** (`toy_not_adequate_after_constant_collapse`).

**Upper bands (C–G, Summit, Instances):** **structures and named obligations** compile; **not** claimed proved except where noted in **`MANIFEST.md`**. Summit **conjectures** are **strong `def` statements** (open).

**SPEC_025 (Instances, N/halting-anchored semantic summit):** **Proved** certificate and transport layer for the halting-anchored **semantic** summit: indexed **Phase D** certificates, **Phase E** reindexing (phantom outer tag) with **groupoid** laws and **section** identities (**`ofSummit_summitReportOf`**, **`ofSummit_summitReportOf_reindex`** along a path, **`ofSummit_summitReportOf_reindex_arbitrary`**), **`Type`** master bundle **`HaltingAnchoredFaithfulSummitMasterBundle`**, and **Phase G** **`NEMSSemanticFaithfulTransport`** linking the bundle to reports, **`outer_from_index`**, and **`as_fourfold_core`**, without packaging EPIC_018 **`SemanticRemainder`** into that **`Type`** (normative multi-lemma API — see **`specs/COMPLETE/SPEC_025_YG2_NEMS_SEMANTIC_GLUE_EPIC.md`**). **Forgetful agreement ⇒ full cited bundle (this track’s “summit”):** if **`summitReportOf (indexed_certificate w_a b₁) = summitReportOf (indexed_certificate w_b b₂)`**, then the two master bundles agree on **`agreed_summit`**, **`summitCert`**, every **`indexed_certificate w₀`**, **`indexed_canonical_certificate`**, the **`as_fourfold_core`** summit-certificate slot, **`to_indexed_canonical_certificate`** / **`ofSummitCert`** on **`summitCert`**, **`agreed_summit` · cascade/tracked**, **`to_summit_only`**, **`cascade_of` / `tracked_of`** on indexed certs, and **`@ofSummit … (agreed_summit)`** at each **`w₀`**. Granular lemmas (e.g. **`agreed_summit_eq_of_summitReportOf_indexed_eq`**, **`summitCert_eq_of_summitReportOf_indexed_eq`**, **`indexed_certificate_eq_of_summitReportOf_indexed_eq`**, **`cascade_of_indexed_eq_of_summitReportOf_indexed_eq`**, **`ofSummit_agreed_eq_of_summitReportOf_indexed_eq`**) remain the ergonomic cite surface; the **single packaging theorem** is **`summitReportOf_indexed_master_agreement_consequences`** — one nested **`∧`** listing all of the above. **Proof engineering:** **`indexed_certificate_eq_of_summitReportOf_indexed_eq`** and **`ofSummit_agreed_eq_of_summitReportOf_indexed_eq`** use **`congrArg`** with a **typed** **`fun r => ⟨r⟩`** packer (not raw **`congrArg @ofSummit`**, which leaves stuck universe metavariables). The **master packaging** proof **inlines** **`summitCert_eq_of_agreed_summit_eq`**, **`eq_of_summitTracked_eq`**, **`congrArg`**, **`rw`**, and **`as_fourfold_core_summitCert.trans`** instead of composing the named **`*_of_summitReportOf_indexed_eq`** theorem **constants** as leaves: reusing those constants inside one large **dependent** **`∧`** type again stuck **`?u`** in the kernel. Elsewhere, proofs favor **`rfl`** / **`congrArg … summit_agrees`** where a single elaborated proof term would otherwise stick universes.

---

## Proof status

**Zero sorry.** **Zero** smuggled conclusions: `AdequacyForcesSomeBurden` is **hypothesis** for abstract B1; **constructed** in `Fin 2` toy.

**SPEC_025 epistemic discipline:** outer faithful remainder is cited as a **sibling** lemma (**`faithful_nems_semantic_remainder_at_unit`**), not as a field of the master bundle; official composition is spelled in the spec’s **§ Official composition API**.

---

## Reproduction

```bash
cd adequacy-architecture-lean
lake update
lake exe cache get
lake build
```

**One-shot from workspace root:** `scripts/verify-lean-build.sh` runs `lake build AdequacyArchitecture` (same target as above). **Citation / provenance:** `../specs/NOTES/LEAN_REPRODUCIBILITY_AND_CITATION.md` under **SPEC_028_EK7** (**COMPLETE**). **Frozen program closure:** `../specs/COMPLETE/SPEC_034_PC7_FINAL_PATH_TO_CLOSURE.md` — **`PROGRAM_CLOSED`** (**§XIV**; **§XV** = post-program; **§XVI** successor pointer). **Canonical active / successor plans (post-034):** `../specs/IN-PROCESS/STATUS_AND_HANDOFF.md` **§0** — not **035** alone: **Universal Coverage** [`SPEC_035_UC1`](../specs/IN-PROCESS/SPEC_035_UC1_UNIVERSAL_COVERAGE_PROGRAM_PHASE1.md) Phase I tranche **frozen**; **Program-1** line **036_FA1** (`G_adm`) through **044_NF4_CUT** (**NF4-C**); **synthesis** [`SPEC_045_AS1`](../specs/IN-PROCESS/SPEC_045_AS1/SPEC_045_AS1_ARCHITECTURE_SYNTHESIS_AND_FLAGSHIP_THEOREM_PROGRAM.md) (integrated theorem / flagship narrative). **Lean cite surface:** `AdequacyArchitecture/Portability/Spec034ProgramClosureLaw.lean` (**`Spec034ProgramClosureLaw`**). **global raw `∀P,B`** = **post-closure** per **SPEC_034**, not the program finish line. **Archived technical spines (SUPERSEDED for obligations):** `../specs/COMPLETE/SPEC_029_FR1_FRONTIER_EXPANSION_BEYOND_EXTERNALIZATION_EPIC.md` (**FE-4+** ladder, **SPEC_033** Rung **F** cites — feeds **M1** packaging); `../specs/COMPLETE/SPEC_021_Q9K_CONDITIONAL_SUMMIT_OUTER_CLOSURE_EPIC.md` — **022** §8 discipline. **Final summit contract (Layer A only):** `../specs/COMPLETE/SPEC_022_HR3_FINAL_CONDITIONAL_SUMMIT_CONTRACT.md` — **COMPLETE**.

---

## Key theorem summary

See **[THEOREM_INVENTORY.md](THEOREM_INVENTORY.md)** and **[MANIFEST.md](MANIFEST.md)**.
