/-
  SPEC_018_S2N — Summit S2 **frontier**: lawful relocation at fixed burden; toy case is **vacuous**
  (no `RelocationPair` for `toyBurden`).

  `BurdenAdmitsRelocation` names the condition under which `UniversalBurdenRelocationLawfulAtBurden B`
  could be **substantive** (open for nontrivial examples).
-/

import AdequacyArchitecture.Lawful.RelocationSummit
import AdequacyArchitecture.Toy.Fin2Model

universe u

namespace AdequacyArchitecture.Lawful

open AdequacyArchitecture.Burden (RelocationPair)
open AdequacyArchitecture.Toy

variable {α : Type u}

/-- Some relocation pair exists for `B` — S2 obligations are not vacuous on antecedent. -/
def BurdenAdmitsRelocation (B : BurdenPredicates α) : Prop :=
  ∃ (f : Transform α) (m₁ m₂ : BurdenMode) (A : Account α), RelocationPair B m₁ m₂ f A

/-- Toy burden: S2 at `B` holds **because** relocation is impossible (`SPEC_018`). -/
theorem universalBurdenRelocationLawfulAtBurden_toyBurden :
    UniversalBurdenRelocationLawfulAtBurden (α := Fin 2) toyBurden :=
  universalBurdenRelocationLawfulAtBurden_of_no_relocation toyBurden
    (fun f m₁ m₂ A h => relocation_pair_toyBurden_false f m₁ m₂ A h)

/-- **Non-vacuous** example (`SPEC_021` CS-2 / `SPEC_018`): `relocDemoBurden` admits a relocation pair
(`sem` along `distinguishingAccount`, landing in `sel` after `constantCollapse`). **Lawful S2 at this burden**
is proved in **`Fin2LawfulRelocationAtBurden.lean`** (`universalBurdenRelocationLawfulAtBurden_relocDemoBurden`). -/
theorem burdenAdmitsRelocation_relocDemoBurden : BurdenAdmitsRelocation relocDemoBurden :=
  ⟨constantCollapse, BurdenMode.sem, BurdenMode.sel, distinguishingAccount, relocationPair_relocDemo_sem_sel⟩

/-- SPEC_023 — `participationDemoBurden` admits relocation (`route → sem` on `constantTrueAccount`). -/
theorem burdenAdmitsRelocation_participationDemoBurden : BurdenAdmitsRelocation participationDemoBurden :=
  ⟨clearSecondFiber, BurdenMode.route, BurdenMode.sem, constantTrueAccount,
    relocationPair_participationDemo_route_sem⟩

end AdequacyArchitecture.Lawful
