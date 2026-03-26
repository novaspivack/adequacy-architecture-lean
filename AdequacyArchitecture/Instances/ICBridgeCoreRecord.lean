/-
  **SPEC_021 CS-3 — IC branch: bridge-core / certification record** (outer closure, IC first).

  **Honest scope.** Faithful IC layers (**`ICFaithful.lean`**) package **`Inner.CertificationLayer`** on
  **`CompressionArchitecture Unit _`** (canonical NEMS spine vs **alt-terminal** spine). The **summit
  proof-essential bridge core** in **`NEMSBridgeCoreRecord.lean`** is stated for **`CorpusStrataCarrier`**
  (= **`Fin 2`**) Adequacy accounts — the **SPEC_013** corridor.

  This module does **not** claim a duplicate **`UniversalBurdenRelocationLawfulAtBurden`** on
  **`CompressionArchitecture`** without a future representation morphism: see module tail for the
  **sharp carrier obstructions**.

  **What we *do* export:** (IC-1) native multiplicity + both faithful **`Nonempty`** layers; (IC-2–IC-4)
  explicit **`(B,P,rcp)`** *on the corpus carrier* aligned with the **Level-2 non-vacuous** NEMS row (same
  honest relocation geometry as **`relocDemoBurden`**); (IC-5) the **proof-essential core** and a **single
  joint bundle** tying IC-native certification to that corridor row.
-/

import AdequacyArchitecture.Instances.ICFaithful
import AdequacyArchitecture.Instances.NEMSBridgeCoreRecord
import InfinityCompression.Meta.NEMSSpineAsArchitecture

namespace AdequacyArchitecture.Instances

open AdequacyArchitecture.Lawful
open ReflexiveArchitecture
open ReflexiveArchitecture.Instances
open InfinityCompression.Meta

/-! ## IC-1 — native multiplicity + faithful `Nonempty` (two certification hosts) -/

/-- **IC-1a.** Canonical vs alt-terminal spine architectures differ (`InfinityCompression.Meta`). -/
theorem ic_native_two_distinct_compression_architectures :
    nemsSpineChain.toArchitecture ≠ nemsSpineChain_altTerminal.toArchitecture :=
  nems_spine_architecture_ne_altTerminal

theorem ic_nonempty_faithful_canonical_certification_layer :
    Nonempty (Inner.CertificationLayer (CompressionArchitecture Unit nemsSpineChain.steps.length)) :=
  nonempty_faithful_ic_nems_spine_certification_layer

theorem ic_nonempty_faithful_alt_terminal_certification_layer :
    Nonempty (Inner.CertificationLayer (CompressionArchitecture Unit nemsSpineChain_altTerminal.steps.length)) :=
  nonempty_faithful_ic_nems_alt_terminal_certification_layer

theorem ic_canonical_faithful_enriched_irreducibility_holds :
    faithfulICNEMSSpineCertificationLayer.EnrichedIrreducibility :=
  faithful_ic_nems_spine_enriched_irreducibility_holds

theorem ic_alt_terminal_faithful_enriched_irreducibility_holds :
    faithfulICNEMSAltTerminalCertificationLayer.EnrichedIrreducibility :=
  faithful_ic_nems_alt_terminal_enriched_irreducibility_holds

/-! ## IC-2 — IC-4 — lawful candidates on **`CorpusStrataCarrier`** (corridor alignment) -/

/--
**B_IC** — lawful burden candidate for the CS-3 IC-aligned row: **definitionally** the corpus NEMS corridor
burden (**`relocDemoBurden`**). The Adequacy carrier for this bridge is **`Fin 2` / `CorpusStrataCarrier`**, not
**`CompressionArchitecture`**.
-/
abbrev icCorpusAlignedBurden : BurdenPredicates CorpusStrataCarrier :=
  corpusNemsFin2Burden

/--
**P_IC** — non-vacuous **final** adequacy on the corridor (**Level 2** row): fiber inequality at **`final`**.
-/
abbrev icCorpusAlignedNonVacuousFinalAdequacy : AdequacyPredicates CorpusStrataCarrier :=
  corpusNemsFin2NonVacuousFinalAdequacy

/-- **rcp_IC** — route profile (**`bothFibersHoldRouteProfile`**). -/
abbrev icCorpusAlignedRouteProfile : RouteConstraintProfile CorpusStrataCarrier :=
  corpusNemsFin2RouteProfile

/-! ## IC-5 — proof-essential bridge core (corpus carrier) -/

theorem ic_cs3_nonempty_relocation_hygiene : NonemptyRelocationForBurden icCorpusAlignedBurden :=
  corpusNemsFin2_nonempty_relocation_hygiene

theorem ic_cs3_lawfulS2 : UniversalBurdenRelocationLawfulAtBurden icCorpusAlignedBurden :=
  corpusNemsFin2_lawfulS2

theorem ic_cs3_final_participation :
    FinalAccountsParticipateInRelocation icCorpusAlignedBurden icCorpusAlignedNonVacuousFinalAdequacy :=
  corpusNemsFin2_nv_final_participation

theorem ic_cs3_route_inhonesty :
    LawfulRouteForcesRcpInhonesty icCorpusAlignedBurden icCorpusAlignedRouteProfile :=
  corpusNemsFin2_nv_route_inhonesty

theorem ic_cs3_nonflat :
    NonFlatFinalityFromRouteConstraintFor icCorpusAlignedNonVacuousFinalAdequacy icCorpusAlignedRouteProfile :=
  corpusNemsFin2_nv_nonflat

/-- **Proof-essential core + non-flat** at **`(icCorpusAlignedBurden, icCorpusAlignedNonVacuousFinalAdequacy, rcp_IC)`**. -/
theorem ic_cs3_proof_essential_bridge_core_and_nonflat :
    UniversalBurdenRelocationLawfulAtBurden icCorpusAlignedBurden ∧
      FinalAccountsParticipateInRelocation icCorpusAlignedBurden icCorpusAlignedNonVacuousFinalAdequacy ∧
        LawfulRouteForcesRcpInhonesty icCorpusAlignedBurden icCorpusAlignedRouteProfile ∧
          NonFlatFinalityFromRouteConstraintFor icCorpusAlignedNonVacuousFinalAdequacy
            icCorpusAlignedRouteProfile :=
  ⟨ic_cs3_lawfulS2, ic_cs3_final_participation, ic_cs3_route_inhonesty, ic_cs3_nonflat⟩

theorem ic_cs3_exists_final_account :
    ∃ A : Account CorpusStrataCarrier, icCorpusAlignedNonVacuousFinalAdequacy.adeq AdeqMode.final A :=
  corpusNemsFin2_nv_exists_final

/-- Full **Level-2-style** conjunction (includes **`∃` final**), same as **`corpusNemsFin2_nv_bridge_core_and_nonflat`**. -/
theorem ic_cs3_nv_bridge_core_and_nonflat :
    (∃ A : Account CorpusStrataCarrier, icCorpusAlignedNonVacuousFinalAdequacy.adeq AdeqMode.final A) ∧
      UniversalBurdenRelocationLawfulAtBurden icCorpusAlignedBurden ∧
        FinalAccountsParticipateInRelocation icCorpusAlignedBurden icCorpusAlignedNonVacuousFinalAdequacy ∧
          LawfulRouteForcesRcpInhonesty icCorpusAlignedBurden icCorpusAlignedRouteProfile ∧
            NonFlatFinalityFromRouteConstraintFor icCorpusAlignedNonVacuousFinalAdequacy
              icCorpusAlignedRouteProfile :=
  corpusNemsFin2_nv_bridge_core_and_nonflat

/-! ## Joint bundle — IC-native certification **and** corridor bridge core (CS-3 deliverable) -/

/--
**Proposition alias** for the joint bundle. Use this on the left of `∧` in further statements: a **theorem**
name denotes a **proof term**, not a `Prop` type, so writing `my_theorem ∧ Q` in a type position mis-elaborates.
-/
def ic_faithful_native_pair_cs3_nv_bridge_core_joint_prop : Prop :=
  (nemsSpineChain.toArchitecture ≠ nemsSpineChain_altTerminal.toArchitecture) ∧
    Nonempty (Inner.CertificationLayer (CompressionArchitecture Unit nemsSpineChain.steps.length)) ∧
      Nonempty (Inner.CertificationLayer (CompressionArchitecture Unit nemsSpineChain_altTerminal.steps.length)) ∧
        faithfulICNEMSSpineCertificationLayer.EnrichedIrreducibility ∧
          faithfulICNEMSAltTerminalCertificationLayer.EnrichedIrreducibility ∧
            NonemptyRelocationForBurden icCorpusAlignedBurden ∧
              UniversalBurdenRelocationLawfulAtBurden icCorpusAlignedBurden ∧
                FinalAccountsParticipateInRelocation icCorpusAlignedBurden
                  icCorpusAlignedNonVacuousFinalAdequacy ∧
                  LawfulRouteForcesRcpInhonesty icCorpusAlignedBurden icCorpusAlignedRouteProfile ∧
                    NonFlatFinalityFromRouteConstraintFor icCorpusAlignedNonVacuousFinalAdequacy
                      icCorpusAlignedRouteProfile

/--
**CS-3 IC joint bundle:** IC’s **native** distinct architectures + both faithful **`Nonempty`** certification
hosts + **EnrichedIrreducibility** on each host + **nonempty** relocation hygiene + **Level-2** bridge core
and **non-flat** on **`CorpusStrataCarrier`**.

This is the maximal **theorem-fed** packaging in this tranche: IC multiplicity is **not** smuggled into
**`BurdenPredicates (CompressionArchitecture …)`**; it **coexists** with the **honest Fin 2** summit row.
-/
theorem ic_faithful_native_pair_cs3_nv_bridge_core_joint : ic_faithful_native_pair_cs3_nv_bridge_core_joint_prop :=
  ⟨ic_native_two_distinct_compression_architectures, ic_nonempty_faithful_canonical_certification_layer,
    ic_nonempty_faithful_alt_terminal_certification_layer, ic_canonical_faithful_enriched_irreducibility_holds,
    ic_alt_terminal_faithful_enriched_irreducibility_holds, ic_cs3_nonempty_relocation_hygiene, ic_cs3_lawfulS2,
    ic_cs3_final_participation, ic_cs3_route_inhonesty, ic_cs3_nonflat⟩

/-! ## Sharp obstruction — lawful row not on the compression carrier (here)

**Diagnosis.** The repository’s lawful relocation theorems for this stack are all built for **`Account
CorpusStrataCarrier`**. Faithful IC **`Inner.CertificationLayer`** is indexed by **`CompressionArchitecture Unit
_`**. There is **no** `BurdenPredicates faithfulIcSpineCompressionArchitecture` in this package whose lawful S2
was derived from IC fields — doing so needs a **chosen** bridge (new burden on that type, or a Strata–Adequacy
compare-map). This is the formal content of “**outer closure** is representation,” not a proof of
impossibility.
-/

end AdequacyArchitecture.Instances
