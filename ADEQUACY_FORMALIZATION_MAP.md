# Adequacy formalization map

**Purpose:** Module roles; pair with `MANIFEST.md` and `THEOREM_INVENTORY.md`.

**Frozen program closure:** `../specs/COMPLETE/SPEC_034_PC7_FINAL_PATH_TO_CLOSURE.md` — **`PROGRAM_CLOSED`** (**M1–M4** + **§XIV**). **Post-034 plans (canonical list):** `../specs/IN-PROCESS/STATUS_AND_HANDOFF.md` **§0** — includes [`SPEC_035_UC1`](../specs/IN-PROCESS/SPEC_035_UC1_UNIVERSAL_COVERAGE_PROGRAM_PHASE1.md) (Phase I tranche **frozen**), **Program-1** arc **036_FA1**–**044_NF4_CUT**, and synthesis [`SPEC_045_AS1`](../specs/IN-PROCESS/SPEC_045_AS1/SPEC_045_AS1_ARCHITECTURE_SYNTHESIS_AND_FLAGSHIP_THEOREM_PROGRAM.md); **not** “**035** only.” **Handoff:** same **`STATUS_AND_HANDOFF`** (**`MASTER_STATUS_AND_HANDOFF.md`** = legacy redirect).  
**Final summit contract (Lean + spec):** `Lawful/FinalConditionalSummit.lean` — [`SPEC_022_HR3`](../specs/COMPLETE/SPEC_022_HR3_FINAL_CONDITIONAL_SUMMIT_CONTRACT.md) (**COMPLETE**). **Raw `∀P,B` / universal RawS1:** **not** this contract’s conclusion — see **`RAW_FRONTIER_SHARP_TARGETS.md`**, **SPEC_029_FR1**.  
**Outsider Stage II spine (prose):** [`SEMANTIC_LIFT_PORTABILITY.md`](../specs/NOTES/SEMANTIC_LIFT_PORTABILITY.md), [`NAPKIN_LAWS_AND_DIAGNOSTICS.md`](../specs/NOTES/NAPKIN_LAWS_AND_DIAGNOSTICS.md) — **FE-4+** / **022** / **RAW_FRONTIER** alignment. **Named-domain second branch:** [`EXTERNAL_CASE_STUDY_NAMED_DOMAIN_TEMPLATE.md`](../specs/NOTES/EXTERNAL_CASE_STUDY_NAMED_DOMAIN_TEMPLATE.md) §4 — **EX-10** [**§ Parallel**](../specs/NOTES/BRANCH_SEMANTIC_TRANSPORT_CHECKLIST.md) + **022** §8.  
**FE-2 / FE-3 + outer accountability:** [`FE2_THEOREM_FED_TRANSPORT_STATUS.md`](../specs/NOTES/FE2_THEOREM_FED_TRANSPORT_STATUS.md), [`FE3_BRANCH_GENERIC_TRANSPORT_AND_FE2_PAYOFF.md`](../specs/NOTES/FE3_BRANCH_GENERIC_TRANSPORT_AND_FE2_PAYOFF.md), [`BRANCH_SEMANTIC_TRANSPORT_CHECKLIST.md`](../specs/NOTES/BRANCH_SEMANTIC_TRANSPORT_CHECKLIST.md) (**SPEC_028** EX-10) — **`From*`** vs **`BranchGenericSemanticTransport`**; **parallel** [`SPEC_021_Q9K`](../specs/COMPLETE/SPEC_021_Q9K_CONDITIONAL_SUMMIT_OUTER_CLOSURE_EPIC.md) + **022** §8.

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
| `AdequacyArchitecture/Summit/*` | S1–S2 conjecture `def`s (open); **`SummitEngine`** (`SPEC_020`); **`UniversalIrreducibleAdequacy`** — S1 target shape vs **`fe4_earned_*`** ladder |
| `AdequacyArchitecture/Portability/*` | **SPEC_034_PC7** program-closure cite surface: **`Spec034ProgramClosureLaw`** (**`M1_from_*`**, **`M2_obstruction_*`**, **`Step4_nativeIcHFinal_iff_spineChecklist`**). **SPEC_028–033 / SPEC_029** transport and gates: **`SummitRowRepresentation`** (**SPEC_032 RQ2**), **`RepresentationCalculusRL9`** (**SPEC_033_RL9** **v2 COMPLETE** — **`CertifiedSummitRowRepresentation`**, IC CS-3 gate, FE-3 joint packs), **`AbsoluteFrontierEarnedToy`** (**SPEC_029 FE-4+** earned RawS1 **A–F** + **`via_rl9_gate`** + **`rungF_proof_irrel`**; **global** **`∀P,B`** post-closure per **034**), **`CorpusConditionalRidgeFrontier`**, **`BranchGenericSemanticTransport`**, etc. — see **`MANIFEST.md`**, **`THEOREM_INVENTORY.md`** |
| `AdequacyArchitecture/Instances/*` | Strata `require` — `Fin 2` corridor (`CorpusDischarge`, embedding + injective), lawful link, lawful representation, **SPEC_013 Phase C** (`CorpusPhaseC`), **LinkedArchitecture** (`LinkedLayer` / cross-corpus `Unit`), faithful NEMS/IC/APS, APS uniformization (`APSIndexedFaithful`), cross-corpus (`FaithfulCorpusJoint`), **HonestyBridge** (Linked vs joint vs `Fin 2`), **UnifiedCarrierMorphisms** (**`SPEC_014_UC1`**) |
| `Instances/ProgramFiniteAdmissibility.lean`, `Program1MetaUnificationMU1.lean`, `Program1OuterGateGrammar.lean`, `Program1LayeredStructureLS1.lean`, `Program1MaximalityMA1.lean`, … | **Program-1 certificate stack** (**SPEC_036_FA1** `Program1FiniteGAdm`; **SPEC_037_MU1**; **SPEC_041_OG1**; **SPEC_042_LS1`; **SPEC_043_SR1** Stage D hooks; **SPEC_044_NF4_CUT**) — **`THEOREM_INVENTORY.md`** |

---

## Strata alignment (names only — see SPEC_001 in `specs/COMPLETE/`)

When wiring imports: `layered_architecture_theorem`, `vanishingCriterion`, `rcsOfMap`, etc. — **never rename**; copy from Strata `MANIFEST.md`.
