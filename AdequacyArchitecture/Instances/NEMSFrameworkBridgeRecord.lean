/-
  **SPEC_024 Level 3 (carrier-native):** bridge-core row on **`faithfulNemsOuterIndexCarrier = NemS.Framework`**.

  This is **not** a morphism from the `Fin 2` corridor: accounts are `Framework → Prop`, and we reuse the
  **two-point relocation shape** from `TwoPointLawfulRelocation` with concrete witnesses
  `haltingFramework` and a **distinct** empty-model framework (`nemsTrivialFramework`).

  **Honesty:** finality / `sem` are tied to **provably distinct framework values**, not to halting truth on
  `Truth M r` — the row is **native to the NEMS index type** while remaining **witness-pair structural**
  (same mathematical spine as `relocDemoBurden`).

  **Heterogeneity (proved below):** `FrameworkHasWorlds haltingFramework` (`haltingFramework_has_worlds`); but
  `¬ FrameworkHasWorlds nemsTrivialFramework` (`not_frameworkHasWorlds_nemsTrivial`). So the **first** Level 3 pair
  (halting vs empty) is **not** two `Truth`-hosts.

  **Level 3b (below):** a second row uses **`haltingFramework`** vs **`fin2HaltingCodeFramework`** (same `eval`/`Truth`
  shape on `Fin 2` codes). **Both** satisfy `FrameworkHasWorlds` (`nems_framework_semantic_pair_both_have_worlds`), but
  the pair still differs only at the **account inequality** spine unless further tied to `Truth` witnesses — see spec.
-/

import AdequacyArchitecture.Instances.UnifiedCarrierMorphisms
import AdequacyArchitecture.Lawful.RelocationAlignedFinality
import AdequacyArchitecture.Lawful.TwoPointLawfulRelocation
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.EquivFin
import NemS.Physical.Instantiation

namespace AdequacyArchitecture.Instances

open AdequacyArchitecture.Lawful
open NemS
open NemS.Physical
open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- `Model = Empty` — disjoint from `haltingFramework.Model = ℕ`. -/
def nemsTrivialFramework : Framework where
  Model := Empty
  Rec := Empty
  Truth := fun m _ => nomatch m

theorem haltingFramework_ne_nemsTrivialFramework : haltingFramework ≠ nemsTrivialFramework := by
  intro h
  have hNatEmpty : ℕ = Empty := congrArg (·.Model) h
  have hn : Nonempty ℕ := inferInstance
  rw [hNatEmpty] at hn
  cases hn with
  | intro x => nomatch x

/-! ### Worlds / records — why the witness pair is semantically asymmetric -/

/-- Minimal “can host `Truth`”: some model and some record (types nonempty). -/
def FrameworkHasWorlds (F : Framework) : Prop :=
  Nonempty F.Model ∧ Nonempty F.Rec

theorem haltingFramework_has_worlds : FrameworkHasWorlds haltingFramework :=
  ⟨Nonempty.intro (Nat.zero : haltingFramework.Model), Nonempty.intro (Nat.zero : haltingFramework.Rec)⟩

theorem not_nonempty_nemsTrivial_model : ¬ Nonempty nemsTrivialFramework.Model
  | ⟨x⟩ => nomatch x

theorem not_nonempty_nemsTrivial_rec : ¬ Nonempty nemsTrivialFramework.Rec
  | ⟨r⟩ => nomatch r

theorem not_frameworkHasWorlds_nemsTrivial : ¬ FrameworkHasWorlds nemsTrivialFramework := by
  rintro ⟨_, hr⟩
  exact not_nonempty_nemsTrivial_rec hr

private theorem nat_ne_fin2 : (ℕ : Type) ≠ Fin 2 := fun h => by
  have hi : Infinite ℕ := inferInstance
  have _ : Infinite (Fin 2) := h ▸ hi
  have : Finite (Fin 2) := inferInstance
  exact not_finite (Fin 2)

/-- `Model = Rec = Fin 2` with the **same halting-style** `Truth` as `haltingFramework`, on `m.val` / `r.val`. -/
noncomputable def fin2HaltingCodeFramework : Framework where
  Model := Fin 2
  Rec := Fin 2
  Truth := fun m r => (eval (Denumerable.ofNat Code m.val) r.val).Dom

theorem haltingFramework_ne_fin2HaltingCodeFramework : haltingFramework ≠ fin2HaltingCodeFramework := fun h =>
  nat_ne_fin2 (congrArg (·.Model) h)

theorem fin2HaltingCodeFramework_has_worlds : FrameworkHasWorlds fin2HaltingCodeFramework :=
  ⟨Nonempty.intro (⟨0, by decide⟩ : fin2HaltingCodeFramework.Model),
    Nonempty.intro (⟨0, by decide⟩ : fin2HaltingCodeFramework.Rec)⟩

/-- First distinguished **`Framework`** (halting instantiation). -/
def nemsFrameworkBridgeI0 : Framework :=
  haltingFramework

/-- Second distinguished **`Framework`** (empty model). -/
def nemsFrameworkBridgeI1 : Framework :=
  nemsTrivialFramework

/-- The bridge’s **second** point is not a second NEMS “world”—no records exist to state `Truth M r`. -/
theorem nems_framework_bridge_i1_has_no_worlds : ¬ FrameworkHasWorlds nemsFrameworkBridgeI1 :=
  not_frameworkHasWorlds_nemsTrivial

theorem nems_framework_bridge_points_ne : nemsFrameworkBridgeI0 ≠ nemsFrameworkBridgeI1 :=
  haltingFramework_ne_nemsTrivialFramework

abbrev nemsFrameworkNativeBurden : BurdenPredicates faithfulNemsOuterIndexCarrier :=
  twoPointBurden nemsFrameworkBridgeI0 nemsFrameworkBridgeI1

def nemsFrameworkNativeNonVacuousFinalAdequacy : AdequacyPredicates faithfulNemsOuterIndexCarrier where
  adeq := fun m A =>
    match m with
    | .final => A nemsFrameworkBridgeI0 ≠ A nemsFrameworkBridgeI1
    | _ => False

abbrev nemsFrameworkNativeRouteProfile : RouteConstraintProfile faithfulNemsOuterIndexCarrier :=
  bothFibersHoldTwoPoint nemsFrameworkBridgeI0 nemsFrameworkBridgeI1 nems_framework_bridge_points_ne

theorem nemsFrameworkNative_lawfulS2 :
    UniversalBurdenRelocationLawfulAtBurden nemsFrameworkNativeBurden :=
  universalBurdenRelocationLawfulAtBurden_twoPoint _ _

theorem nemsFrameworkNative_nonempty_relocation_hygiene :
    NonemptyRelocationForBurden nemsFrameworkNativeBurden :=
  twoPoint_nonempty_relocation _ _ nems_framework_bridge_points_ne

theorem nemsFrameworkNative_exists_final :
    ∃ A : Account faithfulNemsOuterIndexCarrier,
      nemsFrameworkNativeNonVacuousFinalAdequacy.adeq AdeqMode.final A := by
  use distinguishingEqAccount nemsFrameworkBridgeI0
  simp [nemsFrameworkNativeNonVacuousFinalAdequacy, distinguishingEqAccount]
  intro he
  exact nems_framework_bridge_points_ne he.symm

theorem nemsFrameworkNative_final_participation :
    FinalAccountsParticipateInRelocation nemsFrameworkNativeBurden nemsFrameworkNativeNonVacuousFinalAdequacy := by
  intro A hA
  exact ⟨constantCollapseAllTrue, BurdenMode.sem, BurdenMode.sel, relocationPair_twoPoint_sem_sel_of_sem hA⟩

theorem nemsFrameworkNative_route_inhonesty :
    LawfulRouteForcesRcpInhonesty nemsFrameworkNativeBurden nemsFrameworkNativeRouteProfile :=
  lawful_route_forces_inhonesty_twoPoint_bothFibers nems_framework_bridge_points_ne

theorem nemsFrameworkNative_nonflat :
    NonFlatFinalityFromRouteConstraintFor nemsFrameworkNativeNonVacuousFinalAdequacy
      nemsFrameworkNativeRouteProfile :=
  nonFlat_of_lawfulS2_final_participation_and_inhonesty nemsFrameworkNative_lawfulS2
    nemsFrameworkNative_final_participation nemsFrameworkNative_route_inhonesty

theorem nemsFrameworkNative_bridge_core_and_nonflat :
    (∃ A : Account faithfulNemsOuterIndexCarrier, nemsFrameworkNativeNonVacuousFinalAdequacy.adeq AdeqMode.final A) ∧
      UniversalBurdenRelocationLawfulAtBurden nemsFrameworkNativeBurden ∧
        FinalAccountsParticipateInRelocation nemsFrameworkNativeBurden
            nemsFrameworkNativeNonVacuousFinalAdequacy ∧
          LawfulRouteForcesRcpInhonesty nemsFrameworkNativeBurden nemsFrameworkNativeRouteProfile ∧
            NonFlatFinalityFromRouteConstraintFor nemsFrameworkNativeNonVacuousFinalAdequacy
              nemsFrameworkNativeRouteProfile :=
  ⟨nemsFrameworkNative_exists_final, nemsFrameworkNative_lawfulS2, nemsFrameworkNative_final_participation,
    nemsFrameworkNative_route_inhonesty, nemsFrameworkNative_nonflat⟩

theorem nemsFrameworkNative_relocation_aligned : RelocationAlignedWithFinality nemsFrameworkNativeBurden
    nemsFrameworkNativeNonVacuousFinalAdequacy nemsFrameworkNativeRouteProfile :=
  ⟨nemsFrameworkNative_nonempty_relocation_hygiene, nemsFrameworkNative_final_participation,
    nemsFrameworkNative_route_inhonesty⟩

theorem nemsFrameworkNative_nonflat_witness :
    ∃ (A : Account faithfulNemsOuterIndexCarrier),
      nemsFrameworkNativeNonVacuousFinalAdequacy.adeq AdeqMode.final A ∧
        ∃ f : Transform faithfulNemsOuterIndexCarrier, ¬ nemsFrameworkNativeRouteProfile.holds f A := by
  use distinguishingEqAccount nemsFrameworkBridgeI0
  refine And.intro ?_ ?_
  · simp [nemsFrameworkNativeNonVacuousFinalAdequacy, distinguishingEqAccount]
    intro he
    exact nems_framework_bridge_points_ne he.symm
  · use id
    simp [nemsFrameworkNativeRouteProfile, bothFibersHoldTwoPoint, distinguishingEqAccount]
    intro hi
    exact nems_framework_bridge_points_ne hi.symm

/-! ### Level 3b — both witnesses satisfy `FrameworkHasWorlds` (ℕ vs `Fin 2` halting-slice) -/

/-- Semantic-pair left point (= full ℕ halting grid). -/
def nemsSemanticPairI0 : Framework :=
  haltingFramework

noncomputable section

/-- Semantic-pair right point (`Fin 2` grid, same `eval`/`Truth` pattern on `val`). -/
def nemsSemanticPairI1 : Framework :=
  fin2HaltingCodeFramework

abbrev nemsFrameworkSemanticPairBurden : BurdenPredicates faithfulNemsOuterIndexCarrier :=
  twoPointBurden nemsSemanticPairI0 nemsSemanticPairI1

def nemsFrameworkSemanticPairNonVacuousFinalAdequacy : AdequacyPredicates faithfulNemsOuterIndexCarrier where
  adeq := fun m A =>
    match m with
    | .final => A nemsSemanticPairI0 ≠ A nemsSemanticPairI1
    | _ => False

abbrev nemsFrameworkSemanticPairRouteProfile : RouteConstraintProfile faithfulNemsOuterIndexCarrier :=
  bothFibersHoldTwoPoint nemsSemanticPairI0 nemsSemanticPairI1 haltingFramework_ne_fin2HaltingCodeFramework

end

theorem nems_framework_semantic_pair_points_ne : nemsSemanticPairI0 ≠ nemsSemanticPairI1 :=
  haltingFramework_ne_fin2HaltingCodeFramework

theorem nems_framework_semantic_pair_both_have_worlds :
    FrameworkHasWorlds nemsSemanticPairI0 ∧ FrameworkHasWorlds nemsSemanticPairI1 :=
  ⟨haltingFramework_has_worlds, fin2HaltingCodeFramework_has_worlds⟩

theorem nemsFrameworkSemanticPair_lawfulS2 :
    UniversalBurdenRelocationLawfulAtBurden nemsFrameworkSemanticPairBurden :=
  universalBurdenRelocationLawfulAtBurden_twoPoint _ _

theorem nemsFrameworkSemanticPair_nonempty_relocation_hygiene :
    NonemptyRelocationForBurden nemsFrameworkSemanticPairBurden :=
  twoPoint_nonempty_relocation _ _ nems_framework_semantic_pair_points_ne

theorem nemsFrameworkSemanticPair_exists_final :
    ∃ A : Account faithfulNemsOuterIndexCarrier,
      nemsFrameworkSemanticPairNonVacuousFinalAdequacy.adeq AdeqMode.final A := by
  use distinguishingEqAccount nemsSemanticPairI0
  simp [nemsFrameworkSemanticPairNonVacuousFinalAdequacy, distinguishingEqAccount]
  intro he
  exact nems_framework_semantic_pair_points_ne he.symm

theorem nemsFrameworkSemanticPair_final_participation :
    FinalAccountsParticipateInRelocation nemsFrameworkSemanticPairBurden
      nemsFrameworkSemanticPairNonVacuousFinalAdequacy := by
  intro A hA
  exact ⟨constantCollapseAllTrue, BurdenMode.sem, BurdenMode.sel, relocationPair_twoPoint_sem_sel_of_sem hA⟩

theorem nemsFrameworkSemanticPair_route_inhonesty :
    LawfulRouteForcesRcpInhonesty nemsFrameworkSemanticPairBurden nemsFrameworkSemanticPairRouteProfile :=
  lawful_route_forces_inhonesty_twoPoint_bothFibers nems_framework_semantic_pair_points_ne

theorem nemsFrameworkSemanticPair_nonflat :
    NonFlatFinalityFromRouteConstraintFor nemsFrameworkSemanticPairNonVacuousFinalAdequacy
      nemsFrameworkSemanticPairRouteProfile :=
  nonFlat_of_lawfulS2_final_participation_and_inhonesty nemsFrameworkSemanticPair_lawfulS2
    nemsFrameworkSemanticPair_final_participation nemsFrameworkSemanticPair_route_inhonesty

theorem nemsFrameworkSemanticPair_bridge_core_and_nonflat :
    (∃ A : Account faithfulNemsOuterIndexCarrier,
        nemsFrameworkSemanticPairNonVacuousFinalAdequacy.adeq AdeqMode.final A) ∧
      UniversalBurdenRelocationLawfulAtBurden nemsFrameworkSemanticPairBurden ∧
        FinalAccountsParticipateInRelocation nemsFrameworkSemanticPairBurden
            nemsFrameworkSemanticPairNonVacuousFinalAdequacy ∧
          LawfulRouteForcesRcpInhonesty nemsFrameworkSemanticPairBurden nemsFrameworkSemanticPairRouteProfile ∧
            NonFlatFinalityFromRouteConstraintFor nemsFrameworkSemanticPairNonVacuousFinalAdequacy
              nemsFrameworkSemanticPairRouteProfile :=
  ⟨nemsFrameworkSemanticPair_exists_final, nemsFrameworkSemanticPair_lawfulS2,
    nemsFrameworkSemanticPair_final_participation, nemsFrameworkSemanticPair_route_inhonesty,
    nemsFrameworkSemanticPair_nonflat⟩

theorem nemsFrameworkSemanticPair_relocation_aligned : RelocationAlignedWithFinality
    nemsFrameworkSemanticPairBurden nemsFrameworkSemanticPairNonVacuousFinalAdequacy
      nemsFrameworkSemanticPairRouteProfile :=
  ⟨nemsFrameworkSemanticPair_nonempty_relocation_hygiene, nemsFrameworkSemanticPair_final_participation,
    nemsFrameworkSemanticPair_route_inhonesty⟩

theorem nemsFrameworkSemanticPair_nonflat_witness :
    ∃ (A : Account faithfulNemsOuterIndexCarrier),
      nemsFrameworkSemanticPairNonVacuousFinalAdequacy.adeq AdeqMode.final A ∧
        ∃ f : Transform faithfulNemsOuterIndexCarrier, ¬ nemsFrameworkSemanticPairRouteProfile.holds f A := by
  use distinguishingEqAccount nemsSemanticPairI0
  refine And.intro ?_ ?_
  · simp [nemsFrameworkSemanticPairNonVacuousFinalAdequacy, distinguishingEqAccount]
    intro he
    exact nems_framework_semantic_pair_points_ne he.symm
  · use id
    simp [nemsFrameworkSemanticPairRouteProfile, bothFibersHoldTwoPoint, distinguishingEqAccount]
    intro hi
    exact nems_framework_semantic_pair_points_ne hi.symm

end AdequacyArchitecture.Instances
