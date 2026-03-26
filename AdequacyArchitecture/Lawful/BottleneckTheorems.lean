/-
  First two bottleneck theorems over the stratified slice of 𝒞 (SPEC_009).

  (1) Nontrivial lawful burden carrier: canonical carrier from realized burden + variation.
  (2) Relocation witnessed when burden drops at m₁ on f but appears at m₂ on f A.

  Sigma-equivalent bundle `BottleneckOneBundle` + `bottleneck_one_bundle` (SPEC_010 §10).
-/

import AdequacyArchitecture.Core.Basic
import AdequacyArchitecture.Core.Transform
import AdequacyArchitecture.Lawful.StratifiedLawfulArchitecture
import AdequacyArchitecture.Lawful.CanonicalCarrier

universe u

namespace AdequacyArchitecture.Lawful

open AdequacyArchitecture

variable {α : Type u}

/-- Single-valued data for bottleneck 1: mode, accounts, canonical lawful carrier from burden,
and anti-universal burden at the same mode. -/
structure BottleneckOneBundle (𝔖 : StratifiedLawfulAdequacyArchitecture α) where
  mode : BurdenMode
  acc : Account α
  accNeg : Account α
  hBurden : 𝔖.outer.B.burden mode acc
  lawful : LawfulCarrier α
  lawful_is_canonical : lawful = canonicalLawfulCarrierOfBurden 𝔖.outer.B mode acc hBurden
  notBurdenNeg : ¬ 𝔖.outer.B.burden mode accNeg

/-- Canonical bundle from Σ' `burden_variation` (no classical choice). -/
def bottleneck_one_bundle (𝔖 : StratifiedLawfulAdequacyArchitecture α) : BottleneckOneBundle 𝔖 :=
  match 𝔖.burden_variation with
  | ⟨m, ⟨A1, ⟨A2, And.intro hA hNeg⟩⟩⟩ =>
    BottleneckOneBundle.mk m A1 A2 hA (canonicalLawfulCarrierOfBurden 𝔖.outer.B m A1 hA) rfl hNeg

/-- The bundle type is inhabited (sigma corollary). -/
theorem bottleneck_one_nonempty_bundle (𝔖 : StratifiedLawfulAdequacyArchitecture α) :
    Nonempty (BottleneckOneBundle 𝔖) :=
  ⟨bottleneck_one_bundle 𝔖⟩

/-- **Bottleneck 1:** from stratified anti-vacuity, obtain **nonemptiness** of lawful carriers
(from the canonical witness) and an account `A'` with no burden at the same mode — burden
is not globally realized at `m`. -/
theorem bottleneck_one_nontrivial_lawful_carrier (𝔖 : StratifiedLawfulAdequacyArchitecture α) :
    ∃ (m : BurdenMode) (A A' : Account α) (_ : 𝔖.outer.B.burden m A),
      Nonempty (LawfulCarrier α) ∧ ¬ 𝔖.outer.B.burden m A' := by
  let b := bottleneck_one_bundle 𝔖
  exact ⟨b.mode, b.acc, b.accNeg, b.hBurden, ⟨b.lawful⟩, b.notBurdenNeg⟩

/-- Recover bottleneck 1 from any bundle witness. -/
theorem bottleneck_one_nontrivial_lawful_carrier_of_bundle (𝔖 : StratifiedLawfulAdequacyArchitecture α)
    (b : BottleneckOneBundle 𝔖) :
    ∃ (m : BurdenMode) (A A' : Account α) (_ : 𝔖.outer.B.burden m A),
      Nonempty (LawfulCarrier α) ∧ ¬ 𝔖.outer.B.burden m A' :=
  ⟨b.mode, b.acc, b.accNeg, b.hBurden, ⟨b.lawful⟩, b.notBurdenNeg⟩

/-- **Bottleneck 2:** explicit witnesses for drop + reappearance imply `RelocatesBurden`. -/
theorem bottleneck_two_drop_implies_relocates
    (B : BurdenPredicates α) (m₁ m₂ : BurdenMode) (f : Transform α) (A : Account α)
    (h₁ : B.burden m₁ A) (h₂ : ¬ B.burden m₁ (f A)) (h₃ : B.burden m₂ (f A)) :
    RelocatesBurden B m₁ m₂ f :=
  ⟨A, h₁, h₂, h₃⟩

/-- Class-tagged packaging: stratified outer predicates satisfy relocation at witnessed accounts. -/
theorem bottleneck_two_stratified
    (𝔖 : StratifiedLawfulAdequacyArchitecture α) (m₁ m₂ : BurdenMode) (f : Transform α) (A : Account α)
    (h₁ : 𝔖.outer.B.burden m₁ A) (h₂ : ¬ 𝔖.outer.B.burden m₁ (f A)) (h₃ : 𝔖.outer.B.burden m₂ (f A)) :
    RelocatesBurden 𝔖.outer.B m₁ m₂ f :=
  bottleneck_two_drop_implies_relocates 𝔖.outer.B m₁ m₂ f A h₁ h₂ h₃

end AdequacyArchitecture.Lawful
