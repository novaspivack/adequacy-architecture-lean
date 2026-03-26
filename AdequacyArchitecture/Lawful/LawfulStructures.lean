/-
  SPEC_008 — Lawful carrier, route datum, and adequacy architecture (universality class 𝒞).

  Anti-triviality: lawful routes cannot be the all-`True` feature map; lawful architectures
  bundle explicit B1 hypotheses per adequacy mode.

  SPEC_009 — Stratified slice (`StratifiedLawfulAdequacyArchitecture`), canonical carriers
  (`CanonicalCarrier.lean`), and bottleneck theorems refine 𝒞 without smuggling.
-/

import AdequacyArchitecture.Core.Basic
import AdequacyArchitecture.Burden.IrreducibleAdequacy

universe u

namespace AdequacyArchitecture.Lawful

open AdequacyArchitecture.Burden

variable {α : Type u}

/-- Carrier with a **held** witness (content of `Carrier.witness` is true). -/
structure LawfulCarrier (α : Type u) where
  carrier : Carrier α
  witness_holds : carrier.witness

/-- Route datum with **anti-trivial** feature: not every account satisfies `feature`. -/
structure LawfulRouteDatum (α : Type u) where
  datum : RouteDatum α
  nontrivial : ∃ A : Account α, ¬ datum.feature A

/-- Lawful adequacy architecture: every `AdeqMode` is covered by an explicit B1 link
(`AdequacyForcesSomeBurden` at that mode). This is the SPEC_008 universality class 𝒞. -/
structure LawfulAdequacyArchitecture (α : Type u) where
  P : AdequacyPredicates α
  B : BurdenPredicates α
  forces_each : ∀ m : AdeqMode, AdequacyForcesSomeBurden P B m

end AdequacyArchitecture.Lawful
