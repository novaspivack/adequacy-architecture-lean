/-
  **Relocation ↔ finality bridge** (post–`LawfulS2NonFlatOrthogonality`).

  `UniversalBurdenRelocationLawfulAtBurden B` and `NonFlatFinalityFromRouteConstraintFor P rcp` are
  **orthogonal** without extra structure. This module defines **`RelocationAlignedWithFinality`** as a
  **bundle of three named sub-laws** (factorization) and the **repaired** implication.

  **Proof geometry:** `nonFlat_of_lawfulS2_and_relocation_aligned` uses **only** final participation + lawful
  route / `rcp` honesty (`LawfulRouteForcesRcpInhonesty`). **`NonemptyRelocationForBurden`** is
  **summit hygiene**: it rules out vacuous lawful S2 (e.g. `toyBurden`) as *eligible* bridge carriers and is
  **conditionally** redundant once `∃ A, P.final A` and participation hold (`nonempty_relocation_of_…`).
-/

import AdequacyArchitecture.Lawful.RelocationSummit
import AdequacyArchitecture.Lawful.RidgeSummitStatements
import AdequacyArchitecture.Lawful.LawfulStructures
import AdequacyArchitecture.Lawful.SummitS2Frontier
import AdequacyArchitecture.Lawful.LawfulS2NonFlatOrthogonality
import AdequacyArchitecture.Lawful.Fin2LawfulRelocationAtBurden
import AdequacyArchitecture.Lawful.Fin2ParticipationDemoLawful
import AdequacyArchitecture.Toy.Fin2Model

universe u

namespace AdequacyArchitecture.Lawful

open AdequacyArchitecture.Burden (RelocationPair)
open AdequacyArchitecture.Toy
open AdequacyArchitecture.Lawful.FinalConditionalSummit

variable {α : Type u}

/-! ## Factor laws (SPEC_023 — bridge decomposition) -/

/-- **Sub-law 1 — nonempty relocation:** some `RelocationPair` for `B` (alias of `BurdenAdmitsRelocation`). -/
abbrev NonemptyRelocationForBurden (B : BurdenPredicates α) : Prop :=
  BurdenAdmitsRelocation B

/-- **Sub-law 2 — final participation:** every final-adequate account is the **source** of some relocation pair. -/
def FinalAccountsParticipateInRelocation (B : BurdenPredicates α) (P : AdequacyPredicates α) : Prop :=
  ∀ A, P.adeq AdeqMode.final A → ∃ (f : Transform α) (m₁ m₂ : BurdenMode), RelocationPair B m₁ m₂ f A

/-- **Sub-law 3 — lawful route honesty w.r.t. `rcp`:** on every relocation path, **any** lawful witness for S2
forces **`¬ rcp.holds`** on that `(f, A)` (typed bridge; rules out floating `rcp`). -/
def LawfulRouteForcesRcpInhonesty (B : BurdenPredicates α) (rcp : RouteConstraintProfile α) : Prop :=
  ∀ (f : Transform α) (m₁ m₂ : BurdenMode) (A : Account α),
    RelocationPair B m₁ m₂ f A →
      ∀ r : LawfulRouteDatum α,
        r.datum.feature A → r.datum.feature (f A) → ¬ rcp.holds f A

/-- Advisor synonym: honesty of the profile **relative to** lawful relocation (inhonesty = `¬ holds`). -/
abbrev LawfulRelocationRouteHonestyForRcp (B : BurdenPredicates α) (rcp : RouteConstraintProfile α) : Prop :=
  LawfulRouteForcesRcpInhonesty B rcp

/-- **Bundle:** summit-facing alignment = conjunction of the three factor laws. -/
structure RelocationAlignedWithFinality (B : BurdenPredicates α) (P : AdequacyPredicates α)
    (rcp : RouteConstraintProfile α) : Prop where
  nonempty_relocation : NonemptyRelocationForBurden B
  final_participates : FinalAccountsParticipateInRelocation B P
  lawful_route_forces_inhonesty : LawfulRouteForcesRcpInhonesty B rcp

/-! ## Repaired non-flat implication -/

/-- **Minimal hypothesis** for the repaired theorem: lawful S2 + participation + lawful/`rcp` honesty.
`NonemptyRelocationForBurden` is **not** used in this proof (see `nonFlat_of_lawfulS2_and_relocation_aligned`). -/
theorem nonFlat_of_lawfulS2_final_participation_and_inhonesty
    {B : BurdenPredicates α} {P : AdequacyPredicates α} {rcp : RouteConstraintProfile α}
    (hS2 : UniversalBurdenRelocationLawfulAtBurden B)
    (hpart : FinalAccountsParticipateInRelocation B P)
    (hinh : LawfulRouteForcesRcpInhonesty B rcp) :
    NonFlatFinalityFromRouteConstraintFor P rcp := by
  intro hex
  rcases hex with ⟨A0, hA0⟩
  rcases hpart A0 hA0 with ⟨f, m₁, m₂, hrel⟩
  rcases hS2 f m₁ m₂ A0 hrel with ⟨r, hrA, hrFA⟩
  have hnot := hinh f m₁ m₂ A0 hrel r hrA hrFA
  exact ⟨A0, And.intro hA0 ⟨f, hnot⟩⟩

/-- Full bundle ⇒ same conclusion (delegates to the minimal lemma). -/
theorem nonFlat_of_lawfulS2_and_relocation_aligned
    {B : BurdenPredicates α} {P : AdequacyPredicates α} {rcp : RouteConstraintProfile α}
    (hS2 : UniversalBurdenRelocationLawfulAtBurden B)
    (halign : RelocationAlignedWithFinality B P rcp) :
    NonFlatFinalityFromRouteConstraintFor P rcp :=
  nonFlat_of_lawfulS2_final_participation_and_inhonesty hS2 halign.final_participates
    halign.lawful_route_forces_inhonesty

/-- Alias: the same conclusion packaged as a named “bridge hypothesis”. -/
abbrev NonFlatBridgeHypothesis (B : BurdenPredicates α) (P : AdequacyPredicates α)
    (rcp : RouteConstraintProfile α) : Prop :=
  RelocationAlignedWithFinality B P rcp

/-! ## Factor-law algebra -/

theorem relocation_aligned_iff_conj (B : BurdenPredicates α) (P : AdequacyPredicates α)
    (rcp : RouteConstraintProfile α) :
    RelocationAlignedWithFinality B P rcp ↔
      NonemptyRelocationForBurden B ∧ FinalAccountsParticipateInRelocation B P ∧
        LawfulRouteForcesRcpInhonesty B rcp :=
  ⟨(fun h => ⟨h.nonempty_relocation, h.final_participates, h.lawful_route_forces_inhonesty⟩),
    fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- If some final account exists and final participation holds, **`NonemptyRelocationForBurden`** follows —
so the first factor is **redundant** for carriers that already have `∃ A, P.final A` + participation. -/
theorem nonempty_relocation_of_exists_final_and_participates
    {B : BurdenPredicates α} {P : AdequacyPredicates α}
    (hex : ∃ A, P.adeq AdeqMode.final A) (hpart : FinalAccountsParticipateInRelocation B P) :
    NonemptyRelocationForBurden B := by
  rcases hex with ⟨A0, hA0⟩
  rcases hpart A0 hA0 with ⟨f, m₁, m₂, hrel⟩
  exact ⟨f, m₁, m₂, A0, hrel⟩

/-! ### Fieldwise necessity (SPEC_023 — proof-core load-bearing laws)
-/

/-- Route profile: **`holds` iff both fibers** — every `fin2CounterexampleP`-final account passes it on any
`f`, but **`sem` relocation sources** (unequal fibers) force `¬ holds` without quantifying over
`LawfulRouteDatum`. -/
def bothFibersHoldRouteProfile : RouteConstraintProfile (Fin 2) where
  holds := fun _f A => A (⟨0, by decide⟩) ∧ A (⟨1, by decide⟩)
  nontrivial := by
    use distinguishingAccount
    use id
    simp [distinguishingAccount]

private theorem fin2_exists_final_adequacy :
    ∃ A : Account (Fin 2), FinalConditionalSummit.fin2CounterexampleP.adeq AdeqMode.final A := by
  use fun _ => True
  simp [FinalConditionalSummit.fin2CounterexampleP]

private theorem fin2_final_implies_bothFibers_hold (A : Account (Fin 2)) (f : Transform (Fin 2))
    (hf : FinalConditionalSummit.fin2CounterexampleP.adeq AdeqMode.final A) :
    bothFibersHoldRouteProfile.holds f A := by
  simp [FinalConditionalSummit.fin2CounterexampleP, bothFibersHoldRouteProfile] at hf ⊢
  exact hf

theorem not_nonFlat_fin2CounterexampleP_bothFibersHold :
    ¬ NonFlatFinalityFromRouteConstraintFor FinalConditionalSummit.fin2CounterexampleP
      bothFibersHoldRouteProfile := by
  intro h
  rcases fin2_exists_final_adequacy with ⟨A0, hA0⟩
  have h2 := h ⟨A0, hA0⟩
  rcases h2 with ⟨A, ⟨hA, ⟨f, hn⟩⟩⟩
  have holdsA := fin2_final_implies_bothFibers_hold A f hA
  exact hn holdsA

/-- **Sub-law 2 is proof-load-bearing:** lawful S2 + route-honesty (`LawfulRouteForcesRcpInhonesty`) can hold
while **`FinalAccountsParticipateInRelocation` fails** and **`NonFlatFinality…` still fails** (same `P`). -/
theorem lawful_route_forces_inhonesty_relocDemo_bothFibersHold :
    LawfulRouteForcesRcpInhonesty (α := Fin 2) relocDemoBurden bothFibersHoldRouteProfile := by
  intro f m₁ m₂ A hrel r _hrA _hrFA
  rcases relocationPair_relocDemo_only_sem_sel hrel with ⟨rfl, rfl⟩
  rcases hrel with ⟨hsem, _, _⟩
  simp [bothFibersHoldRouteProfile]
  intro h0 h1
  exact hsem (propext (Iff.intro (fun _ => h1) (fun _ => h0)))

theorem not_final_participates_relocDemo_fin2CounterexampleP :
    ¬ FinalAccountsParticipateInRelocation (α := Fin 2) relocDemoBurden
      FinalConditionalSummit.fin2CounterexampleP := by
  intro h
  rcases fin2_exists_final_adequacy with ⟨A0, hA0⟩
  rcases h A0 hA0 with ⟨f, m₁, m₂, hrel⟩
  rcases relocationPair_relocDemo_only_sem_sel hrel with ⟨rfl, rfl⟩
  rcases hrel with ⟨hsem, _, _⟩
  simp [FinalConditionalSummit.fin2CounterexampleP] at hA0
  have : A0 (⟨0, by decide⟩) ↔ A0 (⟨1, by decide⟩) :=
    Iff.intro (fun h0 => hA0.2) (fun h1 => hA0.1)
  exact hsem (propext this)

theorem counterexample_s2_route_inhonesty_without_participation :
    ∃ (B : BurdenPredicates (Fin 2)) (P : AdequacyPredicates (Fin 2)) (rcp : RouteConstraintProfile (Fin 2)),
      UniversalBurdenRelocationLawfulAtBurden B ∧ LawfulRouteForcesRcpInhonesty B rcp ∧
        ¬ FinalAccountsParticipateInRelocation B P ∧
        ¬ NonFlatFinalityFromRouteConstraintFor P rcp :=
  ⟨relocDemoBurden, FinalConditionalSummit.fin2CounterexampleP, bothFibersHoldRouteProfile,
    And.intro universalBurdenRelocationLawfulAtBurden_relocDemoBurden
      (And.intro lawful_route_forces_inhonesty_relocDemo_bothFibersHold
        (And.intro not_final_participates_relocDemo_fin2CounterexampleP
          not_nonFlat_fin2CounterexampleP_bothFibersHold))⟩

theorem not_forall_s2_and_route_inhonesty_implies_nonflat :
    ¬ (∀ (B : BurdenPredicates (Fin 2)) (P : AdequacyPredicates (Fin 2)) (rcp : RouteConstraintProfile (Fin 2)),
        UniversalBurdenRelocationLawfulAtBurden B ∧ LawfulRouteForcesRcpInhonesty B rcp →
          NonFlatFinalityFromRouteConstraintFor P rcp) := by
  intro h
  have := h relocDemoBurden FinalConditionalSummit.fin2CounterexampleP bothFibersHoldRouteProfile
    ⟨universalBurdenRelocationLawfulAtBurden_relocDemoBurden,
      lawful_route_forces_inhonesty_relocDemo_bothFibersHold⟩
  exact not_nonFlat_fin2CounterexampleP_bothFibersHold this

theorem finalAccountsParticipate_participationDemo_fin2CounterexampleP :
    FinalAccountsParticipateInRelocation (α := Fin 2) participationDemoBurden
      FinalConditionalSummit.fin2CounterexampleP := by
  intro A hA
  simp [FinalConditionalSummit.fin2CounterexampleP] at hA
  exact ⟨clearSecondFiber, BurdenMode.route, BurdenMode.sem, relocationPair_participationDemo_route_sem_of hA⟩

theorem not_lawful_route_forces_inhonesty_participationDemo_fin2CounterexampleRcp :
    ¬ LawfulRouteForcesRcpInhonesty (α := Fin 2) participationDemoBurden
      FinalConditionalSummit.fin2CounterexampleRcp := by
  intro h
  have hrel : RelocationPair participationDemoBurden BurdenMode.sem BurdenMode.sel constantCollapse
      distinguishingAccount :=
    relocationPair_participation_sem_sel_iff_relocDemo.mpr relocationPair_relocDemo_sem_sel
  rcases universalBurdenRelocationLawfulAtBurden_participationDemoBurden constantCollapse BurdenMode.sem
      BurdenMode.sel distinguishingAccount hrel with ⟨r, hrA, hrFA⟩
  have hn := h constantCollapse BurdenMode.sem BurdenMode.sel distinguishingAccount hrel r hrA hrFA
  have hm : FinalConditionalSummit.fin2CounterexampleRcp.holds constantCollapse distinguishingAccount := by
    simp [FinalConditionalSummit.fin2CounterexampleRcp, distinguishingAccount]
  exact hn hm

theorem counterexample_s2_participation_without_route_inhonesty :
    ∃ (B : BurdenPredicates (Fin 2)) (P : AdequacyPredicates (Fin 2)) (rcp : RouteConstraintProfile (Fin 2)),
      UniversalBurdenRelocationLawfulAtBurden B ∧ FinalAccountsParticipateInRelocation B P ∧
        ¬ NonFlatFinalityFromRouteConstraintFor P rcp :=
  ⟨participationDemoBurden, FinalConditionalSummit.fin2CounterexampleP,
    FinalConditionalSummit.fin2CounterexampleRcp,
    And.intro universalBurdenRelocationLawfulAtBurden_participationDemoBurden
      (And.intro finalAccountsParticipate_participationDemo_fin2CounterexampleP
        FinalConditionalSummit.not_nonFlat_fin2_counterexample)⟩

theorem counterexample_s2_participation_without_route_inhonesty' :
    ∃ (B : BurdenPredicates (Fin 2)) (P : AdequacyPredicates (Fin 2)) (rcp : RouteConstraintProfile (Fin 2)),
      UniversalBurdenRelocationLawfulAtBurden B ∧ FinalAccountsParticipateInRelocation B P ∧
        ¬ LawfulRouteForcesRcpInhonesty B rcp ∧ ¬ NonFlatFinalityFromRouteConstraintFor P rcp :=
  ⟨participationDemoBurden, FinalConditionalSummit.fin2CounterexampleP,
    FinalConditionalSummit.fin2CounterexampleRcp,
    And.intro universalBurdenRelocationLawfulAtBurden_participationDemoBurden
      (And.intro finalAccountsParticipate_participationDemo_fin2CounterexampleP
        (And.intro not_lawful_route_forces_inhonesty_participationDemo_fin2CounterexampleRcp
          FinalConditionalSummit.not_nonFlat_fin2_counterexample))⟩

theorem not_forall_s2_and_participation_implies_nonflat :
    ¬ (∀ (B : BurdenPredicates (Fin 2)) (P : AdequacyPredicates (Fin 2)) (rcp : RouteConstraintProfile (Fin 2)),
        UniversalBurdenRelocationLawfulAtBurden B ∧ FinalAccountsParticipateInRelocation B P →
          NonFlatFinalityFromRouteConstraintFor P rcp) := by
  intro h
  have := h participationDemoBurden FinalConditionalSummit.fin2CounterexampleP
    FinalConditionalSummit.fin2CounterexampleRcp
    ⟨universalBurdenRelocationLawfulAtBurden_participationDemoBurden,
      finalAccountsParticipate_participationDemo_fin2CounterexampleP⟩
  exact FinalConditionalSummit.not_nonFlat_fin2_counterexample this

/-! ### Hygiene note (sub-law 1)

* **Proof-use:** only **`FinalAccountsParticipateInRelocation`** and **`LawfulRouteForcesRcpInhonesty`** appear in
  `nonFlat_of_lawfulS2_final_participation_and_inhonesty`.
* **`NonemptyRelocationForBurden`:** summit hygiene / anti-vacuity (e.g. exclude `toyBurden` bridges); derivable from
  `∃ final` + participation (`nonempty_relocation_of_exists_final_and_participates`).
-/

theorem not_nonempty_relocation_toyBurden : ¬ NonemptyRelocationForBurden (α := Fin 2) toyBurden := by
  rintro ⟨f, m₁, m₂, A, hp⟩
  exact relocation_pair_toyBurden_false f m₁ m₂ A hp

/-! ### `Fin 2`: counterexample triple fails alignment (structural) -/

/-- `toyBurden` admits **no** relocation pairs — so **no** `RelocationAlignedWithFinality` with any `(P, rcp)`. -/
theorem not_relocation_aligned_toyBurden (P : AdequacyPredicates (Fin 2)) (rcp : RouteConstraintProfile (Fin 2)) :
    ¬ RelocationAlignedWithFinality (α := Fin 2) toyBurden P rcp := by
  intro h
  rcases h.nonempty_relocation with ⟨f, m₁, m₂, A, hp⟩
  exact relocation_pair_toyBurden_false f m₁ m₂ A hp

/-- The previous orthogonality counterexample `(toyBurden, fin2CounterexampleP, fin2CounterexampleRcp)`
cannot satisfy alignment: first conjunct fails. -/
theorem not_relocation_aligned_toy_fin2_counterexample :
    ¬ RelocationAlignedWithFinality (α := Fin 2) toyBurden
      fin2CounterexampleP fin2CounterexampleRcp :=
  not_relocation_aligned_toyBurden _ _

/-- `relocDemoBurden` has a nonempty relocation story (`SPEC_018` witness). -/
theorem relocDemo_nonempty_relocation :
    ∃ (f : Transform (Fin 2)) (m₁ m₂ : BurdenMode) (A : Account (Fin 2)),
      RelocationPair relocDemoBurden m₁ m₂ f A :=
  ⟨constantCollapse, BurdenMode.sem, BurdenMode.sel, distinguishingAccount, relocationPair_relocDemo_sem_sel⟩

theorem relocDemo_nonempty_relocation_for_burden : NonemptyRelocationForBurden (α := Fin 2) relocDemoBurden :=
  burdenAdmitsRelocation_relocDemoBurden

end AdequacyArchitecture.Lawful
