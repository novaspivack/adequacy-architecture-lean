/-
  Corpus discharge — **all** Strata branches (NEMS outer, APS middle, IC inner) on a **shared
  non-`Unit` carrier `Fin 2`, aligned with the Adequacy `Fin 2` toy account model (`Account (Fin 2)`).

  This is **interface instantiation** (Nonempty Strata layers), not full NEMS/APS/IC theorem import:
  those corpora supply proofs **into** the parametric `From*` constructors; here we fix **`S = Fin 2`**
  and discharge the parametric hypotheses with trivial / empty-domain proofs where the interface
  allows it. **`corpus_fin2_index_embedding`** maps `Fin 2` into `ℕ` for comparison with **indexed APS**
  (`APSIndexedFaithful.lean`). See `specs/COMPLETE/SPEC_013_*_CORPUS_DISCHARGE*.md` for mapping + representation.
  **SPEC_035 Program 1:** **`corpusStrataCarrierSwap`** + **`corpusStrataCarrierSwap_involutive`** (involutive compare for **S1a** cleaving).
  **`compareLiftAccountAlong_corpusStrataCarrierSwap`** (*pointwise* — **`NEMSBridgeCoreRecord.lean`**); **`icCs3CompCorpusNvSwap_compareLiftAccountAlong_eq_swap_compareLift`** factors **composed** compare-lift (**`ICCompareRepresentationPullback.lean`**).
-/

import AdequacyArchitecture.Core.Basic
import ReflexiveArchitecture.Instances.FromNEMS
import ReflexiveArchitecture.Instances.FromAPS
import ReflexiveArchitecture.Instances.FromIC

universe u

namespace AdequacyArchitecture.Instances

open ReflexiveArchitecture

/-- Shared Strata carrier for corpus discharge tracks (matches toy `Account (Fin 2)` index). -/
abbrev CorpusStrataCarrier : Type := Fin 2

/-- Embed `Fin 2` account tags into `ℕ` (indexed APS / code indices). For alignment with
`Instances/APSIndexedFaithful.lean` (`IndexedAPS` over `ℕ`). -/
def corpus_fin2_index_embedding : CorpusStrataCarrier → ℕ :=
  fun i => i.val

theorem corpus_fin2_index_embedding_injective : Function.Injective corpus_fin2_index_embedding := by
  intro i j h
  exact Fin.ext h

/-! ### NEMS (outer) — `Th := Empty` so internal theories are vacuous. -/

@[reducible]
def nemsCorpusReflexiveLayer : Outer.ReflexiveLayer CorpusStrataCarrier :=
  Instances.nemsReflexiveLayer CorpusStrataCarrier Empty
    (fun _ => False)
    (fun _ => False)
    (fun _ => True)
    (fun _ => False)
    False
    (fun h => False.elim h)
    (fun T _ _ _ => nomatch T)

theorem nonempty_nems_corpus_outer_layer : Nonempty (Outer.ReflexiveLayer CorpusStrataCarrier) :=
  ⟨nemsCorpusReflexiveLayer⟩

/-! ### APS (middle) — biconditional `True ↔ True ∧ True`. -/

@[reducible]
def apsCorpusRealizationLayer : Middle.RealizationLayer CorpusStrataCarrier :=
  Instances.apsRealizationLayerFromIff CorpusStrataCarrier True True True True (by simp [and_self])

theorem nonempty_aps_corpus_middle_layer : Nonempty (Middle.RealizationLayer CorpusStrataCarrier) :=
  ⟨apsCorpusRealizationLayer⟩

/-! ### IC (inner) — all certification fields `True` with trivial implication axioms. -/

@[reducible]
def icCorpusCertificationLayer : Inner.CertificationLayer CorpusStrataCarrier :=
  Instances.icCertificationLayer CorpusStrataCarrier Unit (fun _ => True) True True True True True True
    True
    (fun _ => trivial) (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)

theorem nonempty_ic_corpus_certification_layer : Nonempty (Inner.CertificationLayer CorpusStrataCarrier) :=
  ⟨icCorpusCertificationLayer⟩

/-- All three Strata layer interfaces are simultaneously inhabited on `CorpusStrataCarrier`. -/
theorem nonempty_strata_corridor_on_corpus_carrier :
    Nonempty (Outer.ReflexiveLayer CorpusStrataCarrier) ∧
    Nonempty (Middle.RealizationLayer CorpusStrataCarrier) ∧
    Nonempty (Inner.CertificationLayer CorpusStrataCarrier) :=
  ⟨nonempty_nems_corpus_outer_layer, nonempty_aps_corpus_middle_layer, nonempty_ic_corpus_certification_layer⟩

/-! ### SPEC_035 — nontrivial involutive compare on **`CorpusStrataCarrier`** (`Fin 2`) -/

/-- Swap the two strata indices (**0 ↔ 1**) on the shared corpus carrier. -/
def corpusStrataCarrierSwap : CorpusStrataCarrier → CorpusStrataCarrier
  | ⟨0, _⟩ => ⟨1, by decide⟩
  | ⟨1, _⟩ => ⟨0, by decide⟩

theorem corpusStrataCarrierSwap_involutive :
    corpusStrataCarrierSwap ∘ corpusStrataCarrierSwap = (id : CorpusStrataCarrier → CorpusStrataCarrier) := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

theorem corpusStrataCarrierSwap_symm {b i : CorpusStrataCarrier} (h : corpusStrataCarrierSwap b = i) :
    b = corpusStrataCarrierSwap i :=
  calc
    b = corpusStrataCarrierSwap (corpusStrataCarrierSwap b) := (congrFun corpusStrataCarrierSwap_involutive b).symm
    _ = corpusStrataCarrierSwap i := congrArg corpusStrataCarrierSwap h

theorem corpusStrataCarrierSwap_injective : Function.Injective corpusStrataCarrierSwap := by
  intro i j h
  calc
    i = corpusStrataCarrierSwap (corpusStrataCarrierSwap i) := (congrFun corpusStrataCarrierSwap_involutive i).symm
    _ = corpusStrataCarrierSwap (corpusStrataCarrierSwap j) := congrArg corpusStrataCarrierSwap h
    _ = j := congrFun corpusStrataCarrierSwap_involutive j

end AdequacyArchitecture.Instances
