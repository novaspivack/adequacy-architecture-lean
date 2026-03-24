/-
  Targets and richness predicates.
  `RichTarget` is intentionally **minimal-commitment**: nontrivial carrier, not the summit richness class.
-/

import Mathlib.Data.Fin.Basic

universe u

namespace AdequacyArchitecture

/-- A target is just a type (objects to be accounted for). -/
abbrev Target (α : Type u) := α

/-- Minimal richness: at least two distinct points (enough for nontrivial distinction). -/
class RichTarget (α : Type u) : Prop where
  exists_pair_ne : ∃ x y : α, x ≠ y

instance fin2_rich : RichTarget (Fin 2) where
  exists_pair_ne := ⟨0, 1, by decide⟩

end AdequacyArchitecture
