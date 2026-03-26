/-
  **SPEC_028_EK7** — domain-neutral **instantiation calculus** (Stage I / Option A).

  **Minimum honest data** to “enter the summit contract” at the **SPEC_008** layer is exactly
  a `LawfulAdequacyArchitecture`. This module packages that obligation for paper-facing narration
  and wires the **S1-shaped master theorem** as a single application.

  Higher tiers (stratified outer ridge, `HFrontier`, semantic transport) import **additional**
  structures — do not fold them into the base definition without upgrading the witness. -/

import AdequacyArchitecture.Lawful.MasterTheorem
import AdequacyArchitecture.Lawful.StratifiedLawfulArchitecture

universe u

namespace AdequacyArchitecture.Portability

open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Summit

variable {α : Type u}

/-- **Summit contract — base layer (SPEC_008 𝒞).**

An external domain exhibits this witness iff it has proved the outer lawful spine:
`∀ m : AdeqMode, AdequacyForcesSomeBurden P B m`. -/
structure SummitContractBase (α : Type u) where
  /-- Lawful adequacy architecture (predicates + B1 at each adequacy mode). -/
  arch : LawfulAdequacyArchitecture α

/-- Construct the packaged contract from an existing lawful architecture (common proof path). -/
def SummitContractBase.ofLawful (𝔸 : LawfulAdequacyArchitecture α) : SummitContractBase α :=
  ⟨𝔸⟩

/-- **Summit S1 shape** for any packaged base contract — **master theorem**, one application. -/
theorem summit_s1_of_base (I : SummitContractBase α) :
    UniversalIrreducibleAdequacyConjecture α I.arch.P I.arch.B :=
  universal_irreducible_adequacy_lawful I.arch

/-- **Stratified** instantiation: SPEC_009 outer + Σ' burden variation (anti-degeneracy). -/
structure StratifiedSummitInstantiation (α : Type u) where
  strat : StratifiedLawfulAdequacyArchitecture α

def StratifiedSummitInstantiation.toBase (S : StratifiedSummitInstantiation α) : SummitContractBase α :=
  ⟨S.strat.outer⟩

theorem summit_s1_of_stratified (S : StratifiedSummitInstantiation α) :
    UniversalIrreducibleAdequacyConjecture α S.strat.outer.P S.strat.outer.B :=
  summit_s1_of_base S.toBase

/-- Paper synonym: same data as `SummitContractBase`. -/
abbrev LawfulSummitInstantiation := SummitContractBase

end AdequacyArchitecture.Portability
