/-
  Canonical lawful carriers born from realized burden (SPEC_009).

  This avoids hand-waving “some carrier exists”: given `B.burden m A`, the witness
  proposition is packaged as `Carrier.witness` with `LawfulCarrier.witness_holds := h`.
-/

import AdequacyArchitecture.Core.Basic
import AdequacyArchitecture.Lawful.LawfulStructures

universe u

namespace AdequacyArchitecture.Lawful

variable {α : Type u}

/-- Tag used for burden-realization carriers (semantic remainder motif). -/
def burdenCarrierTag : CarrierTag := CarrierTag.semanticRemainder

theorem burdenCarrierTag_ne_residual : burdenCarrierTag ≠ CarrierTag.residual := by
  decide

theorem burdenCarrierTag_ne_gluing : burdenCarrierTag ≠ CarrierTag.gluingObstruction := by
  decide

/-- From a realized burden at `(m, A)`, build a `LawfulCarrier` whose witness is exactly that fact. -/
def canonicalLawfulCarrierOfBurden (B : BurdenPredicates α) (m : BurdenMode) (A : Account α)
    (h : B.burden m A) : LawfulCarrier α where
  carrier := { tag := burdenCarrierTag, witness := B.burden m A }
  witness_holds := h

theorem canonicalLawfulCarrierOfBurden_tag (B : BurdenPredicates α) (m : BurdenMode) (A : Account α)
    (h : B.burden m A) :
    (canonicalLawfulCarrierOfBurden B m A h).carrier.tag = burdenCarrierTag :=
  rfl

theorem canonicalLawfulCarrierOfBurden_ne_residual_tag (B : BurdenPredicates α) (m : BurdenMode) (A : Account α)
    (h : B.burden m A) :
    (canonicalLawfulCarrierOfBurden B m A h).carrier.tag ≠ CarrierTag.residual := by
  rw [canonicalLawfulCarrierOfBurden_tag]
  exact burdenCarrierTag_ne_residual

theorem canonicalLawfulCarrierOfBurden_ne_gluing_tag (B : BurdenPredicates α) (m : BurdenMode) (A : Account α)
    (h : B.burden m A) :
    (canonicalLawfulCarrierOfBurden B m A h).carrier.tag ≠ CarrierTag.gluingObstruction := by
  rw [canonicalLawfulCarrierOfBurden_tag]
  exact burdenCarrierTag_ne_gluing

end AdequacyArchitecture.Lawful
