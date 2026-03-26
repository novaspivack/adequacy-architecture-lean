/-
  **SPEC_030_MX7 — Stage B+:** a **fully explicit** `P,B` pair on any carrier `α` such that **B1 fails** at
  **`AdeqMode.repr`**, hence **no** `LawfulAdequacyArchitecture` with that pair, and **¬** summit S1 shape /
  **¬** **`AbsoluteFrontierRawS1`**.

  This tightens the Stage B table: **𝒞** / **`forces_each`** is not merely “narratively nice” — it is **logically
  necessary** for the **proved** master-theorem gate; without it, the **same** `AbsoluteFrontierRawS1` **name**
  can fail.
-/

import AdequacyArchitecture.Burden.IrreducibleAdequacy
import AdequacyArchitecture.Core.Basic
import AdequacyArchitecture.Lawful.FinalConditionalSummit
import AdequacyArchitecture.Lawful.LawfulStructures
import AdequacyArchitecture.Summit.UniversalIrreducibleAdequacy

universe u

namespace AdequacyArchitecture.Portability

open AdequacyArchitecture
open AdequacyArchitecture.Burden
open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open AdequacyArchitecture.Summit

variable {α : Type u}

/-- Adequacy **only** at **`repr`** (every account), all other modes **false**. -/
def s1CounterexampleReprOnlyAdequacy (α : Type u) : AdequacyPredicates α where
  adeq := fun m _ =>
    match m with
    | AdeqMode.repr => True
    | _ => False

/-- Burden **nowhere** holds. -/
def s1CounterexampleEmptyBurden (α : Type u) : BurdenPredicates α where
  burden := fun _ _ => False

/-! ### B1 / 𝒞 failure -/

theorem not_adequacyForcesSomeBurden_reprOnly_empty_repr :
    ¬ AdequacyForcesSomeBurden (s1CounterexampleReprOnlyAdequacy α) (s1CounterexampleEmptyBurden α)
      AdeqMode.repr := by
  intro h
  have hA : (s1CounterexampleReprOnlyAdequacy α).adeq AdeqMode.repr (fun _ : α => True) := trivial
  rcases h (fun _ => True) hA with ⟨m', hm'⟩
  cases m' <;> simp [s1CounterexampleEmptyBurden] at hm'

theorem not_lawfulAdequacyArchitecture_eq_reprOnly_emptyBurden (𝔸 : LawfulAdequacyArchitecture α)
    (hP : 𝔸.P = s1CounterexampleReprOnlyAdequacy α) (hB : 𝔸.B = s1CounterexampleEmptyBurden α) : False := by
  have hf := 𝔸.forces_each AdeqMode.repr
  simp only [hP, hB] at hf
  exact not_adequacyForcesSomeBurden_reprOnly_empty_repr hf

/-! ### Summit S1 shape / Layer-B name -/

theorem not_universalIrreducibleAdequacyCounterexample :
    ¬ UniversalIrreducibleAdequacyConjecture α (s1CounterexampleReprOnlyAdequacy α)
      (s1CounterexampleEmptyBurden α) := by
  intro h
  have hA : (s1CounterexampleReprOnlyAdequacy α).adeq AdeqMode.repr (fun _ : α => True) := trivial
  rcases h AdeqMode.repr (fun _ => True) hA with ⟨m', hm'⟩
  cases m' <;> simp [s1CounterexampleEmptyBurden] at hm'

theorem not_absoluteFrontierRawS1Counterexample :
    ¬ AbsoluteFrontierRawS1 (s1CounterexampleReprOnlyAdequacy α) (s1CounterexampleEmptyBurden α) := by
  simpa [AbsoluteFrontierRawS1] using not_universalIrreducibleAdequacyCounterexample

end AdequacyArchitecture.Portability
