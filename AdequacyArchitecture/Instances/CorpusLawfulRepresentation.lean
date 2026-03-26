/-
  **Representation:** the corpus Strata carrier `CorpusStrataCarrier` is **definitionally** the toy
  account index type `Fin 2`, so the **earned** lawful / stratified / completed toy instances
  (`Toy/Fin2Model.lean`) re-typecheck at `CorpusStrataCarrier` without re-proving.

  This is the formal content behind **`corpus_carrier_eq_toy_account`** (`CorpusLawfulLink.lean`):
  the lawful summit corridor at `toyCompletedStratifiedLawfulAdequacyArchitecture` is the same
  object under the `abbrev` identification `CorpusStrataCarrier = Fin 2`.
-/

import AdequacyArchitecture.Instances.CorpusDischarge
import AdequacyArchitecture.Lawful.CompletedStratified
import AdequacyArchitecture.Toy.Fin2Model

namespace AdequacyArchitecture.Instances

open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Toy

/-- Same lawful spine as `toyLawfulArchitecture`, carried at type `CorpusStrataCarrier` (= `Fin 2`). -/
def corpusToyLawfulArchitecture : LawfulAdequacyArchitecture CorpusStrataCarrier :=
  toyLawfulArchitecture

/-- Stratified lawful instance on the corpus carrier (defeq to toy). -/
def corpusToyStratifiedLawfulAdequacyArchitecture : StratifiedLawfulAdequacyArchitecture CorpusStrataCarrier :=
  toyStratifiedLawfulAdequacyArchitecture

/-- Completed stratified lawful instance on the corpus carrier (defeq to toy). -/
def corpusToyCompletedStratifiedLawfulAdequacyArchitecture :
    CompletedStratifiedLawfulAdequacyArchitecture CorpusStrataCarrier :=
  toyCompletedStratifiedLawfulAdequacyArchitecture

/-- Bottleneck-one bundle at `corpusToyStratifiedLawfulAdequacyArchitecture` (same proof as toy). -/
def corpusToyBottleneckOneBundle : BottleneckOneBundle corpusToyStratifiedLawfulAdequacyArchitecture :=
  toy_bottleneck_one_bundle

/-- Ridge cascade witness at the corpus-identified `𝔠` (same as `toy_ridgeCascadeWitness`). -/
theorem corpus_toy_ridge_cascade_witness :
    RidgeCascadeWitness corpusToyCompletedStratifiedLawfulAdequacyArchitecture :=
  toy_ridgeCascadeWitness

/-- Structural `RidgeBridgeable` at the corpus-identified `𝔠`. -/
theorem corpus_toy_ridge_bridgeable :
    RidgeBridgeable corpusToyCompletedStratifiedLawfulAdequacyArchitecture :=
  toy_ridgeBridgeable

end AdequacyArchitecture.Instances
