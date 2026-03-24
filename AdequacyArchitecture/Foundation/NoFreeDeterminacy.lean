/-
  A4 — No free determinacy: distinctions not internally forced are burden, not “free completion.”
-/

import AdequacyArchitecture.Core.Basic

universe u

namespace AdequacyArchitecture.Foundation

/-- Hidden distinction presented as “free” but not internally forced → classified as burden. -/
theorem hidden_distinction_is_burden {Hidden Forced Burden : Prop}
    (hH : Hidden) (hNF : ¬ Forced) (classify : Hidden → ¬ Forced → Burden) : Burden :=
  classify hH hNF

/-- Template: no “free” determinacy without internal forcing (conclusion is the `Burden` conclusion supplied). -/
theorem no_free_determinacy {D Forced Burden : Prop}
    (hD : D) (hNF : ¬ Forced) (rule : D → ¬ Forced → Burden) : Burden :=
  rule hD hNF

end AdequacyArchitecture.Foundation
