/-
  Infinity Compression (IC) — Strata `ReflexiveArchitecture.Instances.FromIC` provides
  `icCertificationLayer` (IC `require` is transitive via Strata’s `lakefile`).

  **Shared `Fin 2` corpus track:** see `Instances/CorpusDischarge.lean` (`icCorpusCertificationLayer`) and **SPEC_013**. **Faithful (NEMS spine):** `Instances/ICFaithful.lean` — canonical spine + **alt-terminal** spine (`nemsSpineChain_altTerminal`, `faithfulICNEMSAltTerminalCertificationLayer`, `faithful_ic_spine_compression_architectures_ne`). **TODO:** further carriers beyond these two + SPEC_001 import bank.
-/

import AdequacyArchitecture.Core.Basic
import ReflexiveArchitecture.Instances.FromIC

universe u

namespace AdequacyArchitecture.Instances

open ReflexiveArchitecture

/-- Trivial certification layer: all Strata predicates `True`; implications `True → True`. -/
@[reducible]
def trivialCertificationLayer : Inner.CertificationLayer Unit :=
  Instances.icCertificationLayer
    Unit Unit (fun _ => True) True True True True True True True
    (fun _ => trivial) (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)

theorem nonempty_ic_certification_layer : Nonempty (Inner.CertificationLayer Unit) :=
  ⟨trivialCertificationLayer⟩

def ICInstancePlaceholder : Prop := Nonempty (Inner.CertificationLayer Unit)

theorem ic_instance_placeholder_holds : ICInstancePlaceholder :=
  nonempty_ic_certification_layer

end AdequacyArchitecture.Instances
