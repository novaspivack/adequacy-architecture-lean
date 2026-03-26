/-
  SPEC_011 §2.2 + SPEC_012 — Law packages A–C as formal anchors.

  Package A (canonicality): canonical burden carrier tag discipline — always `burdenCarrierTag`.
  Packages B–C are not duplicated as separate Props: their operational content is the SPEC_011
  bridge statements (`RidgeSummitStatements`); see SPEC_012 for the completion table.
-/

import AdequacyArchitecture.Lawful.CompletedStratified
import AdequacyArchitecture.Lawful.CanonicalCarrier

universe u

namespace AdequacyArchitecture.Lawful

open AdequacyArchitecture

variable {α : Type u}

/-- **Package A (canonicality):** every canonical carrier from realized burden uses `burdenCarrierTag`. -/
def CanonicalityLaw (𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α) : Prop :=
  ∀ (m : BurdenMode) (A : Account α) (h : 𝔠.strat.outer.B.burden m A),
    (canonicalLawfulCarrierOfBurden 𝔠.strat.outer.B m A h).carrier.tag = burdenCarrierTag

theorem canonicality_law_holds (𝔠 : CompletedStratifiedLawfulAdequacyArchitecture α) :
    CanonicalityLaw 𝔠 := by
  intro m A h
  exact canonicalLawfulCarrierOfBurden_tag 𝔠.strat.outer.B m A h

end AdequacyArchitecture.Lawful
