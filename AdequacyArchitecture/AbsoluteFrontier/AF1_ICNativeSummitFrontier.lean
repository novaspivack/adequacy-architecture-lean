/-
  **SPEC_027_QX9 — Phase AF-1:** native IC summit frontier (absolute-frontier program, **post-SPEC_026**).

  **Governing question:** Does this increase honest reach toward the strongest over-class theorem — here by
  **removing IC branch asymmetry** at the **`HFinal` / completed-spine** layer?

  **Delivered in this module (dedicated stack — not mixed into NEMS/semantic transport files):**

  1. **Sharp obstruction** on **`icNemsSpineCompressionCarrier`**: `Nonempty (HFinal _)` **iff** a full
     **`CompletedStratifiedLawfulAdequacyArchitecture`** + `(P,rcp)` + ridge + non-flat (instantiation of
     **`HFinal.nonempty_iff`** / **SPEC_026** Phase 1).
  2. **Minimal summit-contract entry** without native `HFinal` on that carrier: the **standard** corpus
     **`icCS3HFinal`** on **`CorpusStrataCarrier`**, bundled with the **SPEC_021** joint
     (**`ic_faithful_native_pair_cs3_nv_bridge_core_joint`**) so native IC certification **coexists** with the
     corridor row — **no** claimed functorial pullback from compression architectures to `Fin 2` burdens here.
  3. **Compare-hook** for future representation pullbacks: **`ICOuterClosureRepresentationCompare`** (map only;
     **`ICNativeOuterClosure`** still owns the TODO for witnessed transport laws).

  **Not claimed:** constructing **`𝔠 : CompletedStratifiedLawfulAdequacyArchitecture icNemsSpineCompressionCarrier`**;
  that remains the honest **native** completion target or a future morphism+predicate story.
-/

import AdequacyArchitecture.Instances.ICNativeOuterClosure
import AdequacyArchitecture.Instances.ICBridgeCoreRecord
import AdequacyArchitecture.Instances.ICSummitRepresentation
import AdequacyArchitecture.Lawful.FinalConditionalSummit

namespace AdequacyArchitecture.AbsoluteFrontier

open AdequacyArchitecture.Instances
open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit

/-! ## AF-1 — obstruction (native compression carrier) -/

/-- **AF-1 obstruction (sharp).** Same content as **`ic_phase1_nonempty_hfinal_iff_spine_data`** — kept here as the
canonical **absolute-frontier** cite for “what is missing for native `HFinal` on the IC spine carrier?”. -/
theorem af1_icNativeCarrier_nonempty_hfinal_iff_spine :
    Nonempty (HFinal icNemsSpineCompressionCarrier) ↔
      ∃ (𝔠 : CompletedStratifiedLawfulAdequacyArchitecture icNemsSpineCompressionCarrier)
        (P : AdequacyPredicates icNemsSpineCompressionCarrier)
        (rcp : RouteConstraintProfile icNemsSpineCompressionCarrier) (_ : RidgeCascadeWitness 𝔠)
        (_ : NonFlatFinalityFromRouteConstraintFor P rcp), True :=
  ic_phase1_nonempty_hfinal_iff_spine_data

/-! ## AF-1 — minimal faithful entry into the final summit contract (corpus row + joint) -/

/--
Bypass witness: **Layer A** summit on **`CorpusStrataCarrier`** + theorem-fed **native/corpus coexistence**
(joint). This is the **minimal honest packaging** in-repo: IC branch **enters** **`FinalConditionalSummit`** via the
**corpus** `HFinal`, not via native compression, while the joint records the **native** certification + bridge core.
-/
structure ICSummitContractBypassWitness where
  corpusHFinal : HFinal CorpusStrataCarrier
  nativeCorpusJoint : ic_faithful_native_pair_cs3_nv_bridge_core_joint_prop
  /-- Standard row: the witness uses **`icCS3HFinal`** (the earned CS-3 packaging). -/
  corpus_is_cs3 : corpusHFinal = icCS3HFinal

/-- Standard bypass (**theorem-fed**). -/
def af1_standard_icSummit_contract_bypass : ICSummitContractBypassWitness where
  corpusHFinal := icCS3HFinal
  nativeCorpusJoint := ic_faithful_native_pair_cs3_nv_bridge_core_joint
  corpus_is_cs3 := rfl

theorem af1_standard_bypass_nonempty : Nonempty ICSummitContractBypassWitness :=
  ⟨af1_standard_icSummit_contract_bypass⟩

/-- **Layer A cascade** from the standard bypass (same as **`ic_cs3_highest_reachable_summit_at`**). -/
theorem af1_standard_bypass_yields_highest_summit :
    MasterStratifiedAdequacyCascadeAt icCS3HFinal.𝔠 icCS3HFinal.P icCS3HFinal.rcp :=
  ic_cs3_highest_reachable_summit_at

/-! ## AF-1 — compare morphism hook (future pullback laws) -/

/-- Repackage **`ICOuterClosureRepresentationCompare`** for the absolute-frontier stack (map-only). -/
abbrev ICNativeSummitCompareMorphism (β : Type) : Type :=
  ICOuterClosureRepresentationCompare β

/-! ## AF-1 — single packaging theorem (obstruction ∧ bypass ∧ cascade) -/

/--
**AF-1 resolution summary** (otherwise-branch, current repo): native `HFinal` on the IC spine compression carrier
is **equivalent** to exhibiting the full spine checklist; **in parallel**, a **nonempty** bypass witness exists and
the **standard** corpus **`HFinal`** yields the **highest reachable** summit at `(𝔠,P,rcp)`.
-/
theorem af1_ic_branch_obstruction_and_standard_summit_entry :
    (Nonempty (HFinal icNemsSpineCompressionCarrier) ↔
        ∃ (𝔠 : CompletedStratifiedLawfulAdequacyArchitecture icNemsSpineCompressionCarrier)
          (P : AdequacyPredicates icNemsSpineCompressionCarrier)
          (rcp : RouteConstraintProfile icNemsSpineCompressionCarrier) (_ : RidgeCascadeWitness 𝔠)
          (_ : NonFlatFinalityFromRouteConstraintFor P rcp), True) ∧
      Nonempty ICSummitContractBypassWitness ∧
      MasterStratifiedAdequacyCascadeAt icCS3HFinal.𝔠 icCS3HFinal.P icCS3HFinal.rcp :=
  And.intro af1_icNativeCarrier_nonempty_hfinal_iff_spine
    (And.intro af1_standard_bypass_nonempty af1_standard_bypass_yields_highest_summit)
