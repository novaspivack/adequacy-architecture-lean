/-
  Lawful S2 and `bothFibers`-style route inhonesty for **two distinguished points** on an arbitrary
  carrier `α`.

  Generalizes `Fin2LawfulRelocationAtBurden` / `relocDemoBurden`: replace `⟨0⟩, ⟨1⟩ : Fin 2` by
  `i0 i1 : α`. Enables **SPEC_024 Level 3** — `α = NemS.Framework` with two provably distinct concrete
  frameworks (halting vs empty-model).
-/

import AdequacyArchitecture.Lawful.RelocationSummit
import AdequacyArchitecture.Lawful.LawfulStructures
import AdequacyArchitecture.Lawful.RidgeSummitStatements
import AdequacyArchitecture.Lawful.RelocationAlignedFinality
import AdequacyArchitecture.Burden.RelocationClass

universe u

namespace AdequacyArchitecture.Lawful

variable {α : Type u}

open AdequacyArchitecture.Burden (RelocationPair)
open Classical

/-- Burden pattern comparing two named points — **same mode split as `relocDemoBurden`** (`sem` / `sel` only). -/
def twoPointBurden (i0 i1 : α) : BurdenPredicates α where
  burden := fun m A =>
    match m with
    | .sem => A i0 ≠ A i1
    | .sel => True
    | _ => False

/-- Mark exactly `i0` with `(· = i0)`; pairs with `i1 ≠ i0` for a `sem` source. -/
def distinguishingEqAccount (i0 : α) : Account α :=
  fun x => x = i0

/-- Collapse every account to `fun _ => True`. -/
def constantCollapseAllTrue : Transform α :=
  fun _ => fun _ => True

theorem relocationPair_twoPoint_only_sem_sel {i0 i1 : α} {f : Transform α} {m₁ m₂ : BurdenMode}
    {A : Account α} (h : RelocationPair (twoPointBurden i0 i1) m₁ m₂ f A) :
    m₁ = BurdenMode.sem ∧ m₂ = BurdenMode.sel := by
  rcases h with ⟨h₁, h₂, h₃⟩
  have hm₁ : m₁ = BurdenMode.sem := by
    cases m₁
    · rfl
    · simp [twoPointBurden] at h₂
    · simp [twoPointBurden] at h₁
    · simp [twoPointBurden] at h₁
    · simp [twoPointBurden] at h₁
    · simp [twoPointBurden] at h₁
  subst hm₁
  have hm₂ : m₂ = BurdenMode.sel := by
    cases m₂
    · exact False.elim (h₂ h₃)
    · rfl
    · simp [twoPointBurden] at h₃
    · simp [twoPointBurden] at h₃
    · simp [twoPointBurden] at h₃
    · simp [twoPointBurden] at h₃
  subst hm₂
  exact ⟨rfl, rfl⟩

def tmplOrFibersTwo (i0 i1 : α) : LawfulRouteDatum α where
  datum := { feature := fun A' => A' i0 ∨ A' i1 }
  nontrivial := by
    use fun _ => False
    intro hfeat
    simp at hfeat

def tmplNotAndTwo (i0 i1 : α) : LawfulRouteDatum α where
  datum := { feature := fun A' => ¬ (A' i0 ∧ A' i1) }
  nontrivial := by
    use fun _x => True
    intro hfeat
    simp at hfeat

noncomputable def lawfulRouteDatum_twoPointPair (i0 i1 : α) (f : Transform α) (A : Account α) :
    LawfulRouteDatum α :=
  if _h : (f A) i0 ∨ (f A) i1 then tmplOrFibersTwo i0 i1 else tmplNotAndTwo i0 i1

theorem sem_burden_implies_or_fibers_two {i0 i1 : α} {A : Account α}
    (hA : (twoPointBurden i0 i1).burden BurdenMode.sem A) :
    A i0 ∨ A i1 := by
  simp [twoPointBurden] at hA
  by_contra hn
  push_neg at hn
  have hiff : A i0 ↔ A i1 :=
    Iff.intro (fun h0 => False.elim (hn.1 h0)) (fun h1 => False.elim (hn.2 h1))
  exact hA hiff

theorem tmplOrFibersTwo_feature {i0 i1 : α} {A : Account α} (hA : A i0 ∨ A i1) :
    (tmplOrFibersTwo i0 i1).datum.feature A := by
  simpa [tmplOrFibersTwo] using hA

theorem tmplOrFibersTwo_feature_f {i0 i1 : α} {f : Transform α} {A : Account α}
    (hfv : (f A) i0 ∨ (f A) i1) :
    (tmplOrFibersTwo i0 i1).datum.feature (f A) := by
  simpa [tmplOrFibersTwo] using hfv

theorem tmplNotAndTwo_feature {i0 i1 : α} {A : Account α}
    (hA : (twoPointBurden i0 i1).burden BurdenMode.sem A) :
    (tmplNotAndTwo i0 i1).datum.feature A := by
  simp [tmplNotAndTwo, twoPointBurden] at hA ⊢
  intro h0 h1
  exact hA (Iff.intro (fun _ => h1) (fun _ => h0))

theorem tmplNotAndTwo_feature_f_of_no_fiber {i0 i1 : α} {f : Transform α} {A : Account α}
    (hnf : ¬ (f A) i0 ∧ ¬ (f A) i1) :
    (tmplNotAndTwo i0 i1).datum.feature (f A) := by
  simp [tmplNotAndTwo]
  intro h0 h1
  exact hnf.1 h0

theorem lawfulRoute_twoPointPair_features (i0 i1 : α) (f : Transform α) (A : Account α)
    (hA : (twoPointBurden i0 i1).burden BurdenMode.sem A)
    (_hf : ¬ (twoPointBurden i0 i1).burden BurdenMode.sem (f A)) :
    let r := lawfulRouteDatum_twoPointPair i0 i1 f A
    r.datum.feature A ∧ r.datum.feature (f A) := by
  dsimp [lawfulRouteDatum_twoPointPair]
  split_ifs with hfv
  · constructor
    · exact tmplOrFibersTwo_feature (sem_burden_implies_or_fibers_two hA)
    · exact tmplOrFibersTwo_feature_f hfv
  · push_neg at hfv
    constructor
    · exact tmplNotAndTwo_feature hA
    · exact tmplNotAndTwo_feature_f_of_no_fiber hfv

/-- Lawful summit S2 at `twoPointBurden i0 i1`. -/
theorem universalBurdenRelocationLawfulAtBurden_twoPoint (i0 i1 : α) :
    UniversalBurdenRelocationLawfulAtBurden (twoPointBurden i0 i1) := by
  intro f m₁ m₂ A h
  rcases relocationPair_twoPoint_only_sem_sel h with ⟨rfl, rfl⟩
  rcases h with ⟨h₁, h₂, _⟩
  use lawfulRouteDatum_twoPointPair i0 i1 f A
  exact lawfulRoute_twoPointPair_features i0 i1 f A h₁ h₂

theorem relocationPair_twoPoint_sem_sel {i0 i1 : α} (h_ne : i0 ≠ i1) :
    RelocationPair (twoPointBurden i0 i1) BurdenMode.sem BurdenMode.sel constantCollapseAllTrue
      (distinguishingEqAccount i0) := by
  refine And.intro ?h1 (And.intro ?h2 ?h3)
  · show (i0 = i0) ≠ (i1 = i0)
    intro he
    refine h_ne ?_
    exact Eq.symm (Iff.mp (Iff.of_eq he) rfl)
  · simp [twoPointBurden, constantCollapseAllTrue]
  · simp [twoPointBurden]

theorem relocationPair_twoPoint_sem_sel_of_sem {i0 i1 : α} {A : Account α}
    (hA : (twoPointBurden i0 i1).burden BurdenMode.sem A) :
    RelocationPair (twoPointBurden i0 i1) BurdenMode.sem BurdenMode.sel constantCollapseAllTrue A := by
  refine And.intro hA (And.intro ?_ ?_)
  · simp [twoPointBurden, constantCollapseAllTrue]
  · simp [twoPointBurden]

theorem twoPoint_nonempty_relocation (i0 i1 : α) (h_ne : i0 ≠ i1) :
    NonemptyRelocationForBurden (twoPointBurden i0 i1) :=
  ⟨constantCollapseAllTrue, BurdenMode.sem, BurdenMode.sel, distinguishingEqAccount i0,
    relocationPair_twoPoint_sem_sel h_ne⟩

def bothFibersHoldTwoPoint (i0 i1 : α) (h_ne : i0 ≠ i1) : RouteConstraintProfile α where
  holds := fun _f A => A i0 ∧ A i1
  nontrivial := by
    use distinguishingEqAccount i0, id
    simp [distinguishingEqAccount]
    intro hi
    exact h_ne hi.symm

theorem lawful_route_forces_inhonesty_twoPoint_bothFibers {i0 i1 : α} (h_ne : i0 ≠ i1) :
    LawfulRouteForcesRcpInhonesty (twoPointBurden i0 i1) (bothFibersHoldTwoPoint i0 i1 h_ne) := by
  intro f m₁ m₂ A hrel r _hrA _hrFA
  rcases relocationPair_twoPoint_only_sem_sel hrel with ⟨rfl, rfl⟩
  rcases hrel with ⟨hsem, _, _⟩
  simp [bothFibersHoldTwoPoint]
  intro h0 h1
  exact hsem (propext (Iff.intro (fun _ => h1) (fun _ => h0)))

end AdequacyArchitecture.Lawful
