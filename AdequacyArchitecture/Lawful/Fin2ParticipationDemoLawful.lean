/-
  SPEC_023 — **Lawful S2 at `participationDemoBurden`** (`Fin 2`).

  Hybrid burden: `relocDemoBurden` + `route = both fibers`. Supports fieldwise counterexamples where
  **`FinalAccountsParticipateInRelocation`** holds for `fin2CounterexampleP` while the standard
  orthogonality `(P, rcp)` still refutes `NonFlatFinality…`.
-/

import AdequacyArchitecture.Lawful.RelocationSummit
import AdequacyArchitecture.Lawful.Fin2LawfulRelocationAtBurden

namespace AdequacyArchitecture.Lawful

open AdequacyArchitecture.Burden (RelocationPair)
open AdequacyArchitecture.Toy
open Classical

private def routeSourceLawfulDatum : LawfulRouteDatum (Fin 2) where
  datum := { feature := fun A' =>
    (A' (⟨0, by decide⟩) ∧ A' (⟨1, by decide⟩)) ∨
      ¬ (A' (⟨0, by decide⟩) ∨ A' (⟨1, by decide⟩)) }
  nontrivial := by
    use distinguishingAccount
    simp [distinguishingAccount]

theorem relocationPair_participation_sem_sel_iff_relocDemo {f : Transform (Fin 2)} {A : Account (Fin 2)} :
    RelocationPair participationDemoBurden BurdenMode.sem BurdenMode.sel f A ↔
      RelocationPair relocDemoBurden BurdenMode.sem BurdenMode.sel f A := by
  simp [RelocationPair, participationDemoBurden, relocDemoBurden]

theorem relocationPair_participationDemo_m1_eq_sem_or_route {m₁ m₂ : BurdenMode} {f : Transform (Fin 2)}
    {A : Account (Fin 2)} (h : RelocationPair participationDemoBurden m₁ m₂ f A) :
    m₁ = BurdenMode.sem ∨ m₁ = BurdenMode.route := by
  cases m₁
  · exact Or.inl rfl
  · simpa [RelocationPair, participationDemoBurden] using h.2.1
  · rcases h with ⟨h1, _, _⟩; cases h1
  · rcases h with ⟨h1, _, _⟩; cases h1
  · rcases h with ⟨h1, _, _⟩; cases h1
  · exact Or.inr rfl

theorem relocationPair_participationDemo_sem_m2 {m₂ : BurdenMode} {f : Transform (Fin 2)} {A : Account (Fin 2)}
    (h : RelocationPair participationDemoBurden BurdenMode.sem m₂ f A) :
    m₂ = BurdenMode.sel ∨ m₂ = BurdenMode.route := by
  cases m₂
  · rcases h with ⟨_, hneg, hpos⟩; exact False.elim (hneg hpos)
  · exact Or.inl rfl
  · rcases h with ⟨_, _, h3⟩; simp [participationDemoBurden] at h3
  · rcases h with ⟨_, _, h3⟩; simp [participationDemoBurden] at h3
  · rcases h with ⟨_, _, h3⟩; simp [participationDemoBurden] at h3
  · exact Or.inr rfl

theorem relocationPair_participationDemo_route_m2 {m₂ : BurdenMode} {f : Transform (Fin 2)} {A : Account (Fin 2)}
    (h : RelocationPair participationDemoBurden BurdenMode.route m₂ f A) :
    m₂ = BurdenMode.sem ∨ m₂ = BurdenMode.sel := by
  cases m₂
  · exact Or.inl rfl
  · exact Or.inr rfl
  · rcases h with ⟨_, _, h3⟩; simp [participationDemoBurden] at h3
  · rcases h with ⟨_, _, h3⟩; simp [participationDemoBurden] at h3
  · rcases h with ⟨_, _, h3⟩; simp [participationDemoBurden] at h3
  · rcases h with ⟨_, hneg, hpos⟩; exact False.elim (hneg hpos)

private theorem sem_implies_or_fibers_participation {A : Account (Fin 2)}
    (hA : participationDemoBurden.burden BurdenMode.sem A) :
    A (⟨0, by decide⟩) ∨ A (⟨1, by decide⟩) := by
  simpa [participationDemoBurden, relocDemoBurden] using sem_burden_implies_or_fibers hA

private theorem not_iff_fibers_implies_or {A : Account (Fin 2)}
    (h : ¬(A (⟨0, by decide⟩) ↔ A (⟨1, by decide⟩))) :
    A (⟨0, by decide⟩) ∨ A (⟨1, by decide⟩) := by
  by_contra hn
  push_neg at hn
  exact h (Iff.intro (fun a0 => False.elim (hn.1 a0)) (fun a1 => False.elim (hn.2 a1)))

private theorem routeSourceLawfulDatum_feature_A {A : Account (Fin 2)}
    (hA : participationDemoBurden.burden BurdenMode.route A) :
    routeSourceLawfulDatum.datum.feature A := by
  simp [routeSourceLawfulDatum, participationDemoBurden] at hA ⊢
  exact Or.inl hA

private theorem routeSourceLawfulDatum_feature_f_of_no_fiber {f : Transform (Fin 2)} {A : Account (Fin 2)}
    (hnf : ¬ (f A) (⟨0, by decide⟩) ∧ ¬ (f A) (⟨1, by decide⟩)) :
    routeSourceLawfulDatum.datum.feature (f A) := by
  simp [routeSourceLawfulDatum]
  exact Or.inr (by simpa using hnf)

/-- **Lawful summit S2** at `participationDemoBurden`. -/
theorem universalBurdenRelocationLawfulAtBurden_participationDemoBurden :
    UniversalBurdenRelocationLawfulAtBurden (α := Fin 2) participationDemoBurden := by
  intro f m₁ m₂ A h
  rcases relocationPair_participationDemo_m1_eq_sem_or_route h with hm₁ | hm₁
  · subst hm₁
    rcases relocationPair_participationDemo_sem_m2 h with hm₂ | hm₂
    · subst hm₂
      rw [relocationPair_participation_sem_sel_iff_relocDemo] at h
      rcases h with ⟨h₁, h₂, _⟩
      use lawfulRouteDatum_relocDemoPair f A
      exact lawfulRoute_relocDemoPair_features f A h₁ h₂
    · subst hm₂
      rcases h with ⟨hA, _hnsem, hrf⟩
      use tmplOrFibers
      refine And.intro (tmplOrFibers_feature (sem_implies_or_fibers_participation hA)) ?_
      exact tmplOrFibers_feature_f (Or.inl hrf.1)
  · subst hm₁
    rcases relocationPair_participationDemo_route_m2 h with hm₂ | hm₂
    · subst hm₂
      rcases h with ⟨hA, hnroute, hsem⟩
      simp [participationDemoBurden] at hA hnroute hsem
      use tmplOrFibers
      refine And.intro ?_ ?_
      · exact tmplOrFibers_feature (Or.inl hA.1)
      · exact tmplOrFibers_feature_f (not_iff_fibers_implies_or hsem)
    · subst hm₂
      rcases h with ⟨hA, hnroute, _⟩
      simp [participationDemoBurden] at hA hnroute
      by_cases hfv : (f A) (⟨0, by decide⟩) ∨ (f A) (⟨1, by decide⟩)
      · use tmplOrFibers
        refine And.intro (tmplOrFibers_feature (Or.inl hA.1)) (tmplOrFibers_feature_f hfv)
      · push_neg at hfv
        use routeSourceLawfulDatum
        refine And.intro (routeSourceLawfulDatum_feature_A hA) ?_
        exact routeSourceLawfulDatum_feature_f_of_no_fiber hfv

end AdequacyArchitecture.Lawful
