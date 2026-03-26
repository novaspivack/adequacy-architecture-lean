/-
  SPEC_018 / SPEC_021 / SPEC_022 — **Lawful S2 at `relocDemoBurden`** on `Fin 2`.

  **Test 1 (chosen):** `UniversalBurdenRelocationLawfulAtBurden relocDemoBurden` — for each `RelocationPair`,
  a `LawfulRouteDatum` is given by two explicit templates (or-branch vs. not-and).

  **Test 2 (not needed):** no obstruction theorem — the per-pair lawful route exists classically on `Fin 2`.
-/

import AdequacyArchitecture.Lawful.RelocationSummit
import AdequacyArchitecture.Toy.Fin2Model

namespace AdequacyArchitecture.Lawful

open AdequacyArchitecture.Burden (RelocationPair)
open AdequacyArchitecture.Toy
open Classical

/-- Every `RelocationPair` for `relocDemoBurden` is **`sem` → `sel`**. -/
theorem relocationPair_relocDemo_only_sem_sel {f : Transform (Fin 2)} {m₁ m₂ : BurdenMode}
    {A : Account (Fin 2)} (h : RelocationPair relocDemoBurden m₁ m₂ f A) :
    m₁ = BurdenMode.sem ∧ m₂ = BurdenMode.sel := by
  rcases h with ⟨h₁, h₂, h₃⟩
  have hm₁ : m₁ = BurdenMode.sem := by
    cases m₁
    · rfl
    · simp [relocDemoBurden] at h₂
    · simp [relocDemoBurden] at h₁
    · simp [relocDemoBurden] at h₁
    · simp [relocDemoBurden] at h₁
    · simp [relocDemoBurden] at h₁
  subst hm₁
  have hm₂ : m₂ = BurdenMode.sel := by
    cases m₂
    · exact False.elim (h₂ h₃)
    · rfl
    · simp [relocDemoBurden] at h₃
    · simp [relocDemoBurden] at h₃
    · simp [relocDemoBurden] at h₃
    · simp [relocDemoBurden] at h₃
  subst hm₂
  exact ⟨rfl, rfl⟩

/-! ### Two lawful route templates (Fin 2)

* **`tmplOrFibers`:** `A' 0 ∨ A' 1` — use when `f A` has **some** true fiber.
* **`tmplNotAnd`:** `¬ (A' 0 ∧ A' 1)` — use when `f A` has **no** true fiber (both false); then `¬ sem (f A)` still holds.
-/

/-- Exported for `Fin2ParticipationDemoLawful` (SPEC_023). -/
def tmplOrFibers : LawfulRouteDatum (Fin 2) where
  datum := { feature := fun A' => A' (⟨0, by decide⟩) ∨ A' (⟨1, by decide⟩) }
  nontrivial := by
    use fun _ => False
    intro hfeat
    simp at hfeat

/-- Exported for reuse on hybrid burdens (SPEC_023). -/
def tmplNotAnd : LawfulRouteDatum (Fin 2) where
  datum := { feature := fun A' => ¬ (A' (⟨0, by decide⟩) ∧ A' (⟨1, by decide⟩)) }
  nontrivial := by
    use fun i => match i with
      | ⟨0, _⟩ => True
      | ⟨1, _⟩ => True
    intro hfeat
    simp at hfeat

/-- If `f A` has some true fiber, use `tmplOrFibers`; else both fibers are false — use `tmplNotAnd`. -/
noncomputable def lawfulRouteDatum_relocDemoPair (f : Transform (Fin 2)) (A : Account (Fin 2)) :
    LawfulRouteDatum (Fin 2) :=
  if h : (f A) (⟨0, by decide⟩) ∨ (f A) (⟨1, by decide⟩) then tmplOrFibers else tmplNotAnd

theorem sem_burden_implies_or_fibers {A : Account (Fin 2)}
    (hA : relocDemoBurden.burden BurdenMode.sem A) :
    A (⟨0, by decide⟩) ∨ A (⟨1, by decide⟩) := by
  simp [relocDemoBurden] at hA
  by_contra hn
  push_neg at hn
  have hiff : A (⟨0, by decide⟩) ↔ A (⟨1, by decide⟩) :=
    Iff.intro (fun h0 => False.elim (hn.1 h0)) (fun h1 => False.elim (hn.2 h1))
  exact hA hiff

theorem tmplOrFibers_feature {A : Account (Fin 2)} (hA : A (⟨0, by decide⟩) ∨ A (⟨1, by decide⟩)) :
    tmplOrFibers.datum.feature A := by
  simpa [tmplOrFibers] using hA

theorem tmplOrFibers_feature_f {f : Transform (Fin 2)} {A : Account (Fin 2)}
    (hfv : (f A) (⟨0, by decide⟩) ∨ (f A) (⟨1, by decide⟩)) :
    tmplOrFibers.datum.feature (f A) := by
  simpa [tmplOrFibers] using hfv

theorem tmplNotAnd_feature {A : Account (Fin 2)}
    (hA : relocDemoBurden.burden BurdenMode.sem A) :
    tmplNotAnd.datum.feature A := by
  simp [tmplNotAnd, relocDemoBurden] at hA ⊢
  intro h0 h1
  exact hA (Iff.intro (fun _ => h1) (fun _ => h0))

theorem tmplNotAnd_feature_f_of_no_fiber {f : Transform (Fin 2)} {A : Account (Fin 2)}
    (hnf : ¬ (f A) (⟨0, by decide⟩) ∧ ¬ (f A) (⟨1, by decide⟩)) :
    tmplNotAnd.datum.feature (f A) := by
  simp [tmplNotAnd]
  intro h0 h1
  exact hnf.1 h0

theorem lawfulRoute_relocDemoPair_features (f : Transform (Fin 2)) (A : Account (Fin 2))
    (hA : relocDemoBurden.burden BurdenMode.sem A)
    (_hf : ¬ relocDemoBurden.burden BurdenMode.sem (f A)) :
    let r := lawfulRouteDatum_relocDemoPair f A
    r.datum.feature A ∧ r.datum.feature (f A) := by
  dsimp [lawfulRouteDatum_relocDemoPair]
  split_ifs with hfv
  · constructor
    · exact tmplOrFibers_feature (sem_burden_implies_or_fibers hA)
    · exact tmplOrFibers_feature_f hfv
  · push_neg at hfv
    constructor
    · exact tmplNotAnd_feature hA
    · exact tmplNotAnd_feature_f_of_no_fiber hfv

/-- **Lawful summit S2** at `relocDemoBurden` (`SPEC_021` CS-2 completion). -/
theorem universalBurdenRelocationLawfulAtBurden_relocDemoBurden :
    UniversalBurdenRelocationLawfulAtBurden (α := Fin 2) relocDemoBurden := by
  intro f m₁ m₂ A h
  rcases relocationPair_relocDemo_only_sem_sel h with ⟨rfl, rfl⟩
  rcases h with ⟨h₁, h₂, _⟩
  use lawfulRouteDatum_relocDemoPair f A
  exact lawfulRoute_relocDemoPair_features f A h₁ h₂

end AdequacyArchitecture.Lawful
