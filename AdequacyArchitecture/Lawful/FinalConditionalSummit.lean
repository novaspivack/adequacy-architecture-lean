/-
  SPEC_022_HR3 — **Final conditional summit** / **highest reachable** (Layer A) interface.

  **Layer A** (`HFinal`, `highestReachable_summit_at`): single minimal honest hypothesis bundle and the
  strongest packaged conclusion currently derivable without smuggling raw `∀ P,B`.

  **Layer B** (`AbsoluteFrontier*`): explicit separation of still-open global / raw targets — not
  claimed by Layer A theorems.

  Burden **`B`** in the informal schema `H(𝔠,P,B)` is fixed by **`𝔠.strat.outer.B`** here; separate
  `B` fields are redundant unless a future alignment predicate is needed for representation work.

  **Lawful S2 vs non-flat:** there is **no** implication from `UniversalBurdenRelocationLawfulAtBurden B` to
  `NonFlatFinalityFromRouteConstraintFor P rcp` without linking hypotheses — see
  `LawfulS2NonFlatOrthogonality.lean` (`not_forall_lawfulS2_implies_nonflat`, `exists_lawfulS2_nonflat_fail`).

  **Repaired bridge:** `RelocationAlignedFinality.lean` — factored sub-laws + **minimal** lemma
  `nonFlat_of_lawfulS2_final_participation_and_inhonesty`, full bundle `nonFlat_of_lawfulS2_and_relocation_aligned` (**SPEC_023**).

  **Summit contract split (SPEC_023 fieldwise pass):**
  * **Proof-essential core:** lawful S2 + `FinalAccountsParticipateInRelocation` + `LawfulRouteForcesRcpInhonesty`
    (lemma `nonFlat_of_lawfulS2_final_participation_and_inhonesty`).
  * **Anti-vacuity / hygiene:** `NonemptyRelocationForBurden` (equivalently `BurdenAdmitsRelocation`) — not used in that
    proof, but excludes vacuous lawful-S2 carriers in honest summit storytelling.
  See `counterexample_s2_route_inhonesty_without_participation`, `counterexample_s2_participation_without_route_inhonesty'`.

  **Known honest instance layer (SPEC_024):** NEMS **SPEC_013 corridor**: **Level 1** `corpusNemsFin2_*` (`toyPred`);
  **Level 2** `corpusNemsFin2_nv_*`.   **Level 3** on `NemS.Framework`: **3a** `nemsFrameworkNative_*`, **3b** `nemsFrameworkSemanticPair_*`
  (`NEMSFrameworkBridgeRecord.lean`; see `SPEC_024_NM1`).   **Semantic glue / Layer A+ (SPEC_025):** `NEMSSemanticGlue.lean`, `NEMSSemanticTracking.lean` (Phase B),
  `NEMSFinalSummitSemanticGlue.lean`, `NEMSFinalSummitLinkedReporting.lean` (Phase C),
  `NEMSSemanticReportCertificate.lean` (Phase D + **F** `halting_anchored_canonical_certificate_summit_agreement`),
  `NEMSSemanticReportCertificateTransport.lean` (Phase E).

  **Outer frontier:** global `AbsoluteFrontier*` defs below; per-corpus gaps remain in the branch table above.
  **Representation → Layer B (earned RawS1 only):** `Portability/SummitRowRepresentation` pullback display ⇒
  **`AbsoluteFrontierRawS1` for that `(P,B)`**; `Portability/RepresentationCalculusRL9` packages compare rows with
  **`CertifiedUpgradeWitness`** and ties **FE-4** Rung **F** (**`fe4_earned_*_via_rl9_gate`**, `AbsoluteFrontierEarnedToy`) — **not** raw **`∀P,B`**.
  **Program closure packaging (`PROGRAM_CLOSED`):** `Portability/Spec034ProgramClosureLaw` — **`M1_*`**, **`M2_obstruction_*`**, **`Step4_nativeIcHFinal_iff_spineChecklist`**.

  **Three-branch closure:** `HFinal.nonempty_iff` (existence checklist on a new carrier);
  **`HFinalWithBranchRole`** — tags relocation/finality vs composition/gluing without changing Layer A theorems.
-/

import AdequacyArchitecture.Lawful.MasterConditionalSummit
import AdequacyArchitecture.Lawful.RidgeSummitStatements
import AdequacyArchitecture.Lawful.RelocationSummit
import AdequacyArchitecture.Summit.SummitOverClass
import AdequacyArchitecture.Summit.SummitBranchRoles
import AdequacyArchitecture.Summit.UniversalIrreducibleAdequacy
import AdequacyArchitecture.Summit.UniversalBurdenRelocation

universe u

namespace AdequacyArchitecture.Lawful

namespace FinalConditionalSummit

open AdequacyArchitecture.Summit

variable {α : Type u}

/-- **\(H_{\mathrm{final}}\)** (minimal Layer A): ridge witness + non-flat finality at `(P, rcp)`.

Proof-essential bridge factors (for documentation; see `RelocationAlignedFinality`): lawful S2, final participation,
`LawfulRouteForcesRcpInhonesty`. Hygiene: `BurdenAdmitsRelocation` / `NonemptyRelocationForBurden`. `HFinal` itself
keeps only `𝔠, P, rcp` plus ridge + non-flat.

* **`ridgeWitness`:** structural content for the SPEC_011 **ridge** segment (`RidgeCascadeWitness`).
* **`nonFlat`:** finality step for the chosen route profile (`NonFlatFinalityFromRouteConstraintFor`).

Outer burden is **`𝔠.strat.outer.B`**; no separate `B` field (see module doc). -/
structure HFinal (α : Type u) where
  𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α
  P : AdequacyPredicates α
  rcp : RouteConstraintProfile α
  ridgeWitness : RidgeCascadeWitness 𝔠
  nonFlat : NonFlatFinalityFromRouteConstraintFor P rcp

/-- Convenience constructor for `HFinal`. -/
def mkHFinal (𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α) (P : AdequacyPredicates α)
    (rcp : RouteConstraintProfile α) (w : RidgeCascadeWitness 𝔠)
    (nf : NonFlatFinalityFromRouteConstraintFor P rcp) : HFinal α :=
  { 𝔠, P, rcp, ridgeWitness := w, nonFlat := nf }

/-- Existence of **`HFinal α`** is **exactly** existence of the spine + `(P,rcp)` + ridge witness + non-flat
(obvious, but **SPEC_026** uses the iff as the sharp “what is missing on a new carrier?” checklist). -/
theorem HFinal.nonempty_iff {α : Type u} :
    Nonempty (HFinal α) ↔
      ∃ (𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α) (P : AdequacyPredicates α)
        (rcp : RouteConstraintProfile α) (_ : RidgeCascadeWitness 𝔠)
        (_ : NonFlatFinalityFromRouteConstraintFor P rcp), True := by
  constructor
  · intro h
    rcases h with ⟨hf⟩
    rcases hf with ⟨𝔠, P, rcp, w, nf⟩
    exact ⟨𝔠, P, rcp, w, nf, trivial⟩
  · rintro ⟨𝔠, P, rcp, w, nf, _⟩ -- `w`,`nf` are the actual summit witnesses for the checklist
    exact ⟨mkHFinal 𝔠 P rcp w nf⟩

/--
**SPEC_026 — role-tagged `HFinal`.** Same Layer-A payload; `branchRole` records whether the honest branch story is
relocation/finality (NEMS/IC corridor style) or composition/gluing (APS middle style). Tags are **metadata** for
closure packaging — they do not alter `highestReachable_summit_at`.
-/
structure HFinalWithBranchRole (α : Type u) where
  toHFinal : HFinal α
  branchRole : SummitBranchRole

/-- Tag a relocation/finality summit row (**NEMS / IC** on a shared lawful carrier such as **`CorpusStrataCarrier`**). -/
def HFinalWithBranchRole.ofRelocationFinality {α : Type u} (h : HFinal α) : HFinalWithBranchRole α :=
  { toHFinal := h, branchRole := SummitBranchRole.relocationFinality }

/--
Tag a row as **composition/gluing** — use only when the mathematical witness is **middle-layer** (e.g. APS indexed
realization). **Do not** use to mis-label a pure relocation corridor `HFinal`.
-/
def HFinalWithBranchRole.ofCompositionGluing {α : Type u} (h : HFinal α) : HFinalWithBranchRole α :=
  { toHFinal := h, branchRole := SummitBranchRole.compositionGluing }

/--
Tag a row as **certification / native-vs-represented** — use when the honest branch content is IC outer-closure /
bridge-core geometry **at** a corpus `HFinal` (**metadata only**; Layer A still uses **`toHFinal`** unchanged).
-/
def HFinalWithBranchRole.ofCertificationRepresentation {α : Type u} (h : HFinal α) :
    HFinalWithBranchRole α :=
  { toHFinal := h, branchRole := SummitBranchRole.certificationRepresentation }

/-- **Primary Layer A theorem:** full `MasterStratifiedAdequacyCascadeAt` from `HFinal`.

This is the **single** summit-shaped conclusion packaging **ridge** + **non-flat** at fixed `(𝔠, P, rcp)`. -/
theorem highestReachable_summit_at (h : HFinal α) :
    MasterStratifiedAdequacyCascadeAt h.𝔠 h.P h.rcp :=
  masterStratifiedAdequacyCascadeAt_of_ridgeCascadeWitness_and_nonFlat h.ridgeWitness h.nonFlat

/-- **Irreducible burden** (summit S1 shape) at the **outer** law package — from `LawfulAdequacyArchitecture`
alone (SPEC_008 / `MasterTheorem`). -/
theorem highestReachable_summit_irreducible (h : HFinal α) :
    SummitS1AtLawful h.𝔠.strat.outer :=
  summitS1_at_lawful h.𝔠.strat.outer

/-- **Route-constraint profile** conjunct is the `CarrierPatternInducesRouteConstraintAt` part of the ridge
segment — already in `MasterStratifiedAdequacyCascadeRidgeAt` (hence in `highestReachable_summit_at`). -/
theorem highestReachable_summit_routeConstraint_embedded (h : HFinal α) :
    CarrierPatternInducesRouteConstraintAt h.𝔠 :=
  (master_conditional_summit_ridge_at h.ridgeWitness).2.2.2

/-- Optional extension: **lawful S2** at the outer burden is an **explicit** extra hypothesis (not forced by
`HFinal`). Use when `UniversalBurdenRelocationLawfulAtBurden 𝔠.strat.outer.B` is available. -/
structure HFinalWithLawfulS2 (α : Type u) extends HFinal α where
  lawfulS2 : UniversalBurdenRelocationLawfulAtBurden 𝔠.strat.outer.B

theorem lawfulS2_of_extended (h : HFinalWithLawfulS2 α) :
    UniversalBurdenRelocationLawfulAtBurden h.𝔠.strat.outer.B :=
  h.lawfulS2

/-- **Weaker** structural input (`RidgeBridgeable`) + non-flat: yields **only** the route-constraint conjunct
via `master_conditional_route_constraint_at_of_ridgeBridgeable`; the remaining ridge conjuncts are **not**
derivable without `RidgeCascadeWitness` (or per-`𝔠` bridge proofs). -/
theorem partial_route_and_nonFlat_of_ridgeBridgeable
    {𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α} {P : AdequacyPredicates α} {rcp : RouteConstraintProfile α}
    (rb : RidgeBridgeable 𝔠) (nf : NonFlatFinalityFromRouteConstraintFor P rcp) :
    CarrierPatternInducesRouteConstraintAt 𝔠 ∧ NonFlatFinalityFromRouteConstraintFor P rcp :=
  And.intro (master_conditional_route_constraint_at_of_ridgeBridgeable rb) nf

/-!
## Layer B — absolute frontier (explicitly not Layer A)

These are **renamed re-exports** of the raw conjecture targets; proving them in full generality remains
outside the current `HFinal` contract.
-/

/-- Raw summit S1 shape over **arbitrary** `P,B` (still conjecture for general predicates). -/
def AbsoluteFrontierRawS1 (P : AdequacyPredicates α) (B : BurdenPredicates α) : Prop :=
  UniversalIrreducibleAdequacyConjecture α P B

/-- Raw summit S2 over **unlawful** `RouteDatum` (global conjecture). -/
def AbsoluteFrontierRawS2 : Prop :=
  @UniversalBurdenRelocationConjecture α

/-- Global lawful S2 over **all** burdens (equivalent to `UniversalBurdenRelocationLawful`; still frontier). -/
def AbsoluteFrontierLawfulS2 : Prop :=
  @UniversalBurdenRelocationLawful α

end FinalConditionalSummit

end AdequacyArchitecture.Lawful
