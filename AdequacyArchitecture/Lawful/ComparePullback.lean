/-
  **SPEC_031_ZK9 — Stage A (generic):** compare-map **pullback** of lawful rows (**𝒞** transport).

  Given **`π : β → α`**, **compare-lift** an account on **`β`** to **`α`** by existential forwarding along fibers
  of **`π`**, then define **`(P,B)`** on **`β`** by evaluating the base predicates on the lifted **`Account α`**.

  **Corollary:** if **`(P,B)`** is lawful on **`α`**, the pulled-back pair is lawful on **`β`** — **no** conditions on **`π`**.

  **SPEC_032 Stage B:** **`compareLiftAccountAlong`** is **injective** on native accounts when **`π`** is **injective**
  (**`compareLiftAccountAlong_injective_of_injective_pi`**); constant **`π`** remains the sharp collapse regime
  (**`compareLiftAccountAlong_collapses_of_constant`**). Indexed **FE-3** / **`PhantomReindexLayer`** functoriality along
  **`π`** is still **branch-specific** (not packaged here).
-/

import AdequacyArchitecture.Core.Adequacy
import AdequacyArchitecture.Core.Burden
import AdequacyArchitecture.Burden.IrreducibleAdequacy
import AdequacyArchitecture.Lawful.LawfulStructures

universe u

namespace AdequacyArchitecture

variable {α β : Type u}

/-- **Compare-lift:** push an **`Account β`** forward to **`Account α`** along fibers of **`π`**. -/
def compareLiftAccountAlong (π : β → α) (Aβ : Account β) : Account α :=
  fun a => ∃ b : β, π b = a ∧ Aβ b

/-- Pull back **adequacy** predicates along **`π`**. -/
def AdequacyPredicates.pullbackAlongCompare (P : AdequacyPredicates α) (π : β → α) : AdequacyPredicates β where
  adeq m Aβ := P.adeq m (compareLiftAccountAlong π Aβ)

/-- Pull back **burden** predicates along **`π`**. -/
def BurdenPredicates.pullbackAlongCompare (B : BurdenPredicates α) (π : β → α) : BurdenPredicates β where
  burden m Aβ := B.burden m (compareLiftAccountAlong π Aβ)

/--
**SPEC_031 Stage B (generic obstruction):** a **constant** compare map sends **all** fibers to **`c`**. If **`β`**
carries two distinct points, some **distinct** **`Account β`** become **indistinguishable** after
**`compareLiftAccountAlong π`** — **injective** native account content is **lost** at the **`Account α`** target.

**Interpretation:** one cannot treat **`compareLift`** as a **general** Grothendieck-style section of accounts along an
arbitrary compare — in particular **not** along the IC Stage-D **constant** `compareToCorpus`. Rich
**`BranchGenericSemanticTransport.IndexedPhantomCertificateOps`** are **not** induced here; only the **Unit** trivial
**`Core` / `fe3TrivialUnitCore` remains carrier-agnostic by definition (`BranchGenericSemanticTransport`).
-/
theorem compareLiftAccountAlong_collapses_of_constant {α β : Type u} (π : β → α) (c : α) (hπ : ∀ b : β, π b = c)
    (hb : ∃ b₁ b₂ : β, b₁ ≠ b₂) :
    ∃ A₁ A₂ : Account β, A₁ ≠ A₂ ∧ compareLiftAccountAlong π A₁ = compareLiftAccountAlong π A₂ := by
  rcases hb with ⟨b₁, b₂, hb⟩
  refine ⟨fun x => x = b₁, fun x => x = b₂, ?_, ?_⟩
  · rintro he
    apply hb
    have h := congrFun he b₁
    rw [eq_true (Eq.refl b₁)] at h
    exact of_eq_true (Eq.symm h)
  · funext a
    simp only [compareLiftAccountAlong]
    apply propext
    by_cases ha : a = c
    · subst ha
      refine iff_of_true ?_ ?_
      · exact ⟨b₁, hπ b₁, rfl⟩
      · exact ⟨b₂, hπ b₂, rfl⟩
    · refine iff_of_false ?_ ?_
      · rintro ⟨b, hbπ, _⟩
        rw [hπ] at hbπ
        exact ha hbπ.symm
      · rintro ⟨b, hbπ, _⟩
        rw [hπ] at hbπ
        exact ha hbπ.symm

/-- Compare-lift along **`id`** is the identity on **`Account α`**. -/
theorem compareLiftAccountAlong_id (α : Type u) (A : Account α) :
    compareLiftAccountAlong (id : α → α) A = A := by
  funext x
  simp only [compareLiftAccountAlong]
  apply propext
  constructor
  · rintro ⟨b, hb, hAb⟩
    subst hb
    exact hAb
  · intro hx
    exact ⟨x, rfl, hx⟩

theorem AdequacyPredicates.pullbackAlongCompare_id (P : AdequacyPredicates α) :
    P.pullbackAlongCompare (id : α → α) = P := by
  rcases P with ⟨adeq⟩
  dsimp [AdequacyPredicates.pullbackAlongCompare]
  congr 1
  funext m A
  rw [compareLiftAccountAlong_id]

theorem BurdenPredicates.pullbackAlongCompare_id (B : BurdenPredicates α) :
    B.pullbackAlongCompare (id : α → α) = B := by
  rcases B with ⟨burden⟩
  dsimp [BurdenPredicates.pullbackAlongCompare]
  congr 1
  funext m A
  rw [compareLiftAccountAlong_id]

/--
**SPEC_032 Stage B:** at **`a := π b`**, compare-lift evaluates on the **native fiber** (unique by **`π`** injective).
-/
theorem compareLiftAccountAlong_apply_of_injective {β α : Type u} (π : β → α) (hπ : Function.Injective π)
    (A : Account β) (b : β) : compareLiftAccountAlong π A (π b) = A b := by
  dsimp [compareLiftAccountAlong]
  apply propext
  constructor
  · rintro ⟨b', hbπ, hAb'⟩
    have hb' : b' = b := hπ hbπ
    subst hb'
    exact hAb'
  · intro h
    exact ⟨b, rfl, h⟩

/--
**SPEC_032 Stage B:** injective compare **reflects** native **accounts** — dual regime to constant-map **collapse**.
-/
theorem compareLiftAccountAlong_injective_of_injective_pi {α β : Type u} {π : β → α} (hπ : Function.Injective π) :
    Function.Injective (compareLiftAccountAlong π) := by
  intro A₁ A₂ he
  funext b
  have h := congrFun he (π b)
  rwa [compareLiftAccountAlong_apply_of_injective π hπ A₁ b, compareLiftAccountAlong_apply_of_injective π hπ A₂ b] at h

end AdequacyArchitecture

namespace AdequacyArchitecture.Lawful

open AdequacyArchitecture

variable {α β : Type u}

/-- **𝒞 transport:** lawfulness on **`α`** implies lawfulness of the **compare pullback** on **`β`**. -/
def lawfulAdequacyArchitecture_pullbackAlongCompare (π : β → α) (arch : LawfulAdequacyArchitecture α) :
    LawfulAdequacyArchitecture β where
  P := arch.P.pullbackAlongCompare π
  B := arch.B.pullbackAlongCompare π
  forces_each := fun m Aβ hP => arch.forces_each m (compareLiftAccountAlong π Aβ) hP

end AdequacyArchitecture.Lawful
