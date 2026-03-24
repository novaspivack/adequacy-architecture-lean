/-
  A1 — Adequacy interface: existence of a typed adequacy family + mode comparison/transport scaffolding.
-/

import AdequacyArchitecture.Core.Basic

universe u

namespace AdequacyArchitecture.Foundation

variable {α : Type u}

/-- Bundled interface data (the “lawful” spine; extend with transports as the program strengthens). -/
structure AdequacyInterface (α : Type u) where
  preds : AdequacyPredicates α

/-- **Existence** of *some* interface (minimal — vacuous adequacy everywhere). Not the summit; a size-`Nonempty` anchor. -/
def trivialInterface (α : Type u) : AdequacyInterface α :=
  ⟨{ adeq := fun _ _ => False }⟩

theorem adequacy_interface_exists (α : Type u) : Nonempty (AdequacyInterface α) :=
  ⟨trivialInterface α⟩

/-- Nondegenerate: some mode admits adequacy somewhere (positive content). -/
def InterfaceNondegenerate (I : AdequacyInterface α) : Prop :=
  ∃ (m : AdeqMode) (A : Account α), I.preds.adeq m A

/-- Transport statement template: relating two modes along a target isomorphism (strengthen later with `Equiv α β`). -/
def AdequacyModesComparable (_I : AdequacyInterface α) : Prop :=
  ∀ _ _ : AdeqMode, True

theorem modes_comparable_of_trivial (I : AdequacyInterface α) (_h : ∀ m A, ¬ I.preds.adeq m A) :
    AdequacyModesComparable I := fun _ _ => trivial

end AdequacyArchitecture.Foundation
