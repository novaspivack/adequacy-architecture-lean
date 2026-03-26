/-
  SPEC_016_R2F — **Higher summit elevation (earned ridge discharge):** repackage machine-checked
  `MasterStratifiedAdequacyCascadeRidgeAt` / `RidgeCascadeWitness` for the **toy** `𝔠` and the
  **corpus-named** `𝔠` (defeq to toy via `CorpusLawfulRepresentation`).
-/

import AdequacyArchitecture.Instances.CorpusPhaseC
import AdequacyArchitecture.Lawful.RidgeBridgeable
import AdequacyArchitecture.Lawful.RidgeSummitStatements
import AdequacyArchitecture.Toy.Fin2Model

namespace AdequacyArchitecture.Lawful

open AdequacyArchitecture.Instances
open AdequacyArchitecture.Toy

/-- SPEC_011 ridge segment at the **toy** completed stratified instance (`SPEC_016`). -/
theorem higherSummit_ridge_discharge_toy :
    MasterStratifiedAdequacyCascadeRidgeAt toyCompletedStratifiedLawfulAdequacyArchitecture :=
  toy_masterStratifiedAdequacyCascadeRidgeAt

/-- Full `RidgeCascadeWitness` at the toy `𝔠`. -/
theorem higherSummit_ridge_cascade_witness_toy :
    RidgeCascadeWitness toyCompletedStratifiedLawfulAdequacyArchitecture :=
  toy_ridgeCascadeWitness

/-- Same ridge segment at the **corpus-identified** completed instance (`CorpusPhaseC`). -/
theorem higherSummit_ridge_discharge_corpus :
    MasterStratifiedAdequacyCascadeRidgeAt corpusToyCompletedStratifiedLawfulAdequacyArchitecture :=
  corpus_phaseC_master_stratified_adequacy_cascade_ridge

/-- Master cascade at toy `𝔠` including `NonFlat` step for `toyPred` (fixed `rcp`). -/
theorem higherSummit_master_stratified_cascade_at_toy (rcp : RouteConstraintProfile (Fin 2)) :
    MasterStratifiedAdequacyCascadeAt toyCompletedStratifiedLawfulAdequacyArchitecture toyPred rcp :=
  toy_masterStratifiedAdequacyCascadeAt rcp

end AdequacyArchitecture.Lawful
