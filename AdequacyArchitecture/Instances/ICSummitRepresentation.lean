/-
  **SPEC_021 CS-3 — IC summit representation map** (`H_final` / final contract anchoring).

  **`ICBridgeCoreRecord.lean`** packages IC-native **certification multiplicity** with the **corpus**
  **`(B_IC, P_IC, rcp_IC)`** row on **`CorpusStrataCarrier`**. Here we record how that row sits under
  **`FinalConditionalSummit`**’s **`HFinal`** interface: one **theorem-fed** **`HFinal CorpusStrataCarrier`**
  instance built from the **earned** corpus **`𝔠`** + **Level-2 non-vacuous** `(P,rcp)` + **ridge witness** +
  **non-flat**.

  **What does *not* happen here:** an **`HFinal (CompressionArchitecture Unit _)`** — there is still **no**
  **`CompletedStratifiedLawfulAdequacyArchitecture`** on the IC compression carrier in this repository
  (**sharp outer-closure / representation gap**; see **`ICBridgeCoreRecord`** obstructions doc).

  **Lawful S2 note.** The outer burden **`𝔠.strat.outer.B`** on the corpus toy is **`toyBurden`** (only **`sem`**
  substantive); lawful S2 there is the **vacuous** no-relocation pattern. The **non-vacuous** lawful S2 for
  **`relocDemoBurden`** (**`B_IC`**) is **`ic_cs3_lawfulS2`** (**`ICBridgeCoreRecord`**).
-/

import AdequacyArchitecture.Instances.ICBridgeCoreRecord
import AdequacyArchitecture.Instances.CorpusLawfulRepresentation
import AdequacyArchitecture.Instances.CorpusDischarge
import AdequacyArchitecture.Lawful.FinalConditionalSummit
import AdequacyArchitecture.Lawful.SummitS2Frontier
import AdequacyArchitecture.Toy.Fin2Model

namespace AdequacyArchitecture.Instances

open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open AdequacyArchitecture.Summit
open AdequacyArchitecture.Toy

/--
**IC CS-3 — `HFinal` on the corpus carrier:** same spine as **`corpusToyCompletedStratifiedLawfulAdequacyArchitecture`**
with **non-vacuous final adequacy** and the **corridor** route profile; ridge witness = corpus toy cascade;
non-flat = **`ic_cs3_nonflat`**.
-/
def icCS3HFinal : HFinal CorpusStrataCarrier :=
  mkHFinal corpusToyCompletedStratifiedLawfulAdequacyArchitecture icCorpusAlignedNonVacuousFinalAdequacy
    icCorpusAlignedRouteProfile corpus_toy_ridge_cascade_witness ic_cs3_nonflat

/-- **Layer A conclusion:** full **`MasterStratifiedAdequacyCascadeAt`** from **`icCS3HFinal`**. -/
theorem ic_cs3_highest_reachable_summit_at :
    MasterStratifiedAdequacyCascadeAt icCS3HFinal.𝔠 icCS3HFinal.P icCS3HFinal.rcp :=
  highestReachable_summit_at icCS3HFinal

theorem ic_cs3_summit_irreducible_at_lawful :
    SummitS1AtLawful icCS3HFinal.𝔠.strat.outer :=
  highestReachable_summit_irreducible icCS3HFinal

/--
Lawful S2 at the **outer** burden of **`icCS3HFinal`**: **vacuous** on relocation antecedent (**`toyBurden`**
pattern on **`CorpusStrataCarrier`**).
-/
theorem ic_cs3_lawfulS2_at_outer_toy_burden :
    UniversalBurdenRelocationLawfulAtBurden icCS3HFinal.𝔠.strat.outer.B :=
  universalBurdenRelocationLawfulAtBurden_of_no_relocation icCS3HFinal.𝔠.strat.outer.B fun f m₁ m₂ A h =>
    relocation_pair_toyBurden_false f m₁ m₂ A (by
      simpa [icCS3HFinal, corpusToyCompletedStratifiedLawfulAdequacyArchitecture,
        corpusToyStratifiedLawfulAdequacyArchitecture, corpusToyLawfulArchitecture, CorpusStrataCarrier] using h)

/-- **Non-vacuous** lawful S2 for the **IC-aligned corridor burden** **`relocDemoBurden`** (`B_IC`). -/
theorem ic_cs3_lawfulS2_at_ic_aligned_corridor_burden :
    UniversalBurdenRelocationLawfulAtBurden icCorpusAlignedBurden :=
  ic_cs3_lawfulS2

/--
**Extended Layer-A shape** (ridge + non-flat + **explicit** lawful S2 at the outer toy burden).
-/
def icCS3HFinalWithLawfulS2 : HFinalWithLawfulS2 CorpusStrataCarrier where
  toHFinal := icCS3HFinal
  lawfulS2 := ic_cs3_lawfulS2_at_outer_toy_burden

/-- CS-3 joint reference: IC-native NV bridge-core record (`joint_prop`) plus Layer-A cascade at `icCS3HFinal`. -/
theorem ic_cs3_faithful_bundle_highest_summit_at :
    ic_faithful_native_pair_cs3_nv_bridge_core_joint_prop ∧
      MasterStratifiedAdequacyCascadeAt icCS3HFinal.𝔠 icCS3HFinal.P icCS3HFinal.rcp :=
  And.intro ic_faithful_native_pair_cs3_nv_bridge_core_joint ic_cs3_highest_reachable_summit_at

end AdequacyArchitecture.Instances
