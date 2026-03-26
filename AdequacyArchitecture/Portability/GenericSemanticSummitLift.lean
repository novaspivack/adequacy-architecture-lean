/-
  **SPEC_030_MX7 — Stage C (v1):** branch-generic **joint semantic law** — **Layer-A summit** packaging
  (**`HFinalWithBranchRole`**) together with an **FE-3** **`Core`** yields, **in parallel** and **without**
  identifying lawful cascade content with the transport report codomain **`R`**,

  1. **`MasterStratifiedAdequacyCascadeAt`** from **`highestReachable_summit_at`**, and
  2. forgetful **indexed coherence** + **agreement injectivity** on the **`Core`**.

  This is the honest abstract “semantic lift” scaffold **above FE-3**: **NEMS** (and other branches) supply
  **richer** `W,B,IC,R` and **`PhantomReindexLayer`** data; the joint law **specializes** with those witnesses
  (see **`Instances/NEMSBranchGenericSemanticTransport.lean`**).
-/

import AdequacyArchitecture.Lawful.FinalConditionalSummit
import AdequacyArchitecture.Portability.BranchGenericSemanticTransport
import AdequacyArchitecture.Summit.SummitBranchRoles

universe u

namespace AdequacyArchitecture.Portability

open AdequacyArchitecture.Lawful
open AdequacyArchitecture.Lawful.FinalConditionalSummit
open AdequacyArchitecture.Portability.BranchGenericSemanticTransport

variable {α : Type u}

abbrev Fe3UnitCore :=
  Core Unit Unit (fun _ : Unit => True) True

/--
**Stage C package:** role-tagged **Layer A** summit + **FE-3** head (principal API uses **`Unit`** phantom like
**Stage A/B** certified row transport slot; richer **`Core`** families instantiate the same lemmas **mutatis
mutandis** at the types they carry).
-/
structure SummitFE3SemanticPackage (α : Type u) where
  summitTagged : HFinalWithBranchRole α
  fe3 : Fe3UnitCore

theorem summitFE3_forgetful_discipline (p : SummitFE3SemanticPackage α) :
    ForgetfulIndexedCoherent p.fe3.ops ∧ ForgetfulAgreementInjects p.fe3.ops :=
  And.intro p.fe3.forget_coherent p.fe3.forget_injects

theorem summitFE3_summit_cascade (p : SummitFE3SemanticPackage α) :
    MasterStratifiedAdequacyCascadeAt p.summitTagged.toHFinal.𝔠 p.summitTagged.toHFinal.P
      p.summitTagged.toHFinal.rcp :=
  highestReachable_summit_at p.summitTagged.toHFinal

/--
**Generic joint law** — cascade **∧** forgetful discipline; **no** morphism tying **`R`** to **`Truth`**, **`P.final`**,
or outer **Strata** bands.
-/
theorem summitFE3_joint_semantic_law (p : SummitFE3SemanticPackage α) :
    MasterStratifiedAdequacyCascadeAt p.summitTagged.toHFinal.𝔠 p.summitTagged.toHFinal.P
        p.summitTagged.toHFinal.rcp ∧
      ForgetfulIndexedCoherent p.fe3.ops ∧ ForgetfulAgreementInjects p.fe3.ops :=
  And.intro (summitFE3_summit_cascade p) (summitFE3_forgetful_discipline p)

@[simp] theorem summitFE3_summit_cascade_left (p : SummitFE3SemanticPackage α) :
    (summitFE3_joint_semantic_law p).left = summitFE3_summit_cascade p :=
  rfl

@[simp] theorem summitFE3_forgetful_discipline_and (p : SummitFE3SemanticPackage α) :
    (summitFE3_joint_semantic_law p).right = summitFE3_forgetful_discipline p :=
  rfl

end AdequacyArchitecture.Portability
