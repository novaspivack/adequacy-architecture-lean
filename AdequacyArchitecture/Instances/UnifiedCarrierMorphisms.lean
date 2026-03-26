/-
  **Unified carrier scope** — how **`Fin 2`**, **`Unit`**, and **faithful indices** (`Framework`, NEMS spine
  `CompressionArchitecture`) sit in one story **without** identifying them.

  ## What is formalized

  * **Named Strata index types** (`corpusStrataIndexCarrier`, `linkedStrataIndexCarrier`,
    `faithfulApsMiddleIndexCarrier`, `faithfulNemsOuterIndexCarrier`, `faithfulIcSpineCompressionArchitecture`,
    `faithfulIcAltTerminalCompressionArchitecture`) — abbreviations only; **`not_exists_distinct_pair_*`** on `Unit`
    (no NEMS-style two-point witness pair on APS middle).
  * **Terminal collapse** `CorpusStrataCarrier → Unit` — the unique map from any type to `Unit` (forgets the
    toy dichotomy).
  * **Obstruction:** no function `Fin 2 → Unit` is **injective** — collapse cannot preserve distinct
    `Fin 2` accounts (contrast `corpus_fin2_index_embedding` into `ℕ`, which **is** injective).
  * **Contrast:** `Fin 2` has two distinct inhabitants.

  ## What is *not* claimed

  * No definitional isomorphism `Fin 2 ≃ Framework`, no canonical `Framework → Fin 2`, no commuting diagram
    tying the **corpus toy corridor** to the **halting framework** or **IC spine** — those live on different
    Strata type parameters by design (`SPEC_014_UC1`, `HonestyBridge.lean`).

  See **`specs/COMPLETE/SPEC_014_UC1_UNIFIED_CARRIER_MORPHISM_SCOPE.md`** for obligations and frontier.
-/

import AdequacyArchitecture.Instances.CorpusDischarge
import AdequacyArchitecture.Instances.NEMSFaithful
import AdequacyArchitecture.Instances.ICFaithful

universe u

namespace AdequacyArchitecture.Instances

open InfinityCompression.Meta

/-- Strata outer/middle/inner index for SPEC_013 **`Fin 2`** corridor (`CorpusDischarge`). -/
abbrev corpusStrataIndexCarrier : Type := CorpusStrataCarrier

/-- Strata index for **`LinkedArchitecture Unit`** (`LinkedLayer`; **APS** cross-corpus middle is also `Unit`). -/
abbrev linkedStrataIndexCarrier : Type := Unit

/-- APS EPIC cross-corpus middle — same type as `linkedStrataIndexCarrier` (`APSFaithful.lean`). -/
abbrev faithfulApsMiddleIndexCarrier : Type := Unit

/-- Strata index for faithful NEMS outer layer (`NEMSFaithful` — `Outer.ReflexiveLayer` at `NemS.Framework`). -/
abbrev faithfulNemsOuterIndexCarrier := NemS.Framework

/-- IC inner layer index on the NEMS spine (`ICFaithful` — same spine as `DirectCrossCorpusBridge`). -/
abbrev faithfulIcSpineCompressionArchitecture :=
  CompressionArchitecture Unit nemsSpineChain.steps.length

/-- Second IC-native host: alt-terminal spine (`nemsSpineChain_altTerminal`), same length, **not** equal to the
canonical spine (`faithful_ic_spine_compression_architectures_ne`). -/
abbrev faithfulIcAltTerminalCompressionArchitecture :=
  CompressionArchitecture Unit nemsSpineChain_altTerminal.steps.length

/-- Canonical NEMS spine architecture and the alt-terminal spine differ (`SPEC_024` IC second witness). -/
theorem faithful_ic_spine_compression_architectures_ne :
    nemsSpineChain.toArchitecture ≠ nemsSpineChain_altTerminal.toArchitecture :=
  nems_spine_architecture_ne_altTerminal

/-- Terminal collapse: toy / corpus account carrier maps to the linked cross-corpus singleton index. -/
def collapseCorpusStrataCarrierToLinked (_ : CorpusStrataCarrier) : Unit :=
  ()

theorem collapse_corpus_strata_carrier_eq_const :
    collapseCorpusStrataCarrierToLinked = fun _ : CorpusStrataCarrier => () :=
  rfl

/-- Every function to `Unit` is equal pointwise (codomain subsingleton). -/
theorem eq_of_fun_to_unit {α : Type u} (f g : α → Unit) : f = g := by
  funext x
  cases f x
  cases g x
  rfl

/-- Hence there is only one function `α → Unit` up to equality. -/
theorem unique_fun_to_unit {α : Type u} (f : α → Unit) : f = fun _ => () := by
  funext x
  cases f x
  rfl

theorem fin2_zero_ne_one : (0 : Fin 2) ≠ 1 := by decide

/-- **`Unit`** carries **at most one** inhabitant — no ordered pair `i0 ≠ i1` for the NEMS Level 3
`twoPointBurden` witness pattern (`Lawful/TwoPointLawfulRelocation.lean`). -/
theorem not_exists_distinct_pair_unit :
    ¬ ∃ (i0 i1 : Unit), i0 ≠ i1 :=
  fun ⟨i0, i1, hne⟩ => hne (Subsingleton.elim i0 i1)

theorem not_exists_distinct_pair_linked_index :
    ¬ ∃ (i0 i1 : linkedStrataIndexCarrier), i0 ≠ i1 :=
  not_exists_distinct_pair_unit

theorem not_exists_distinct_pair_faithful_aps_middle :
    ¬ ∃ (i0 i1 : faithfulApsMiddleIndexCarrier), i0 ≠ i1 :=
  not_exists_distinct_pair_unit

/-- Collapse to `Unit` cannot be injective on `Fin 2`: two accounts become indistinguishable. -/
theorem not_injective_fin2_to_unit (f : Fin 2 → Unit) : ¬ Function.Injective f := fun h =>
  absurd (h (Subsingleton.elim (f 0) (f 1))) fin2_zero_ne_one

/-- Embedding into `ℕ` *does* separate the two corpus indices (`CorpusDischarge`). -/
theorem corpus_fin2_index_embedding_injective' :
    Function.Injective corpus_fin2_index_embedding :=
  corpus_fin2_index_embedding_injective

end AdequacyArchitecture.Instances
