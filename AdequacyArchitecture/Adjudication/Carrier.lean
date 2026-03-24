/-
  Adjudicative carrier class (abstract).
-/

import AdequacyArchitecture.Core.Basic

universe u

namespace AdequacyArchitecture.Adjudication

structure AdjudicativeCarrier ( _α : Type u) where
  witness : Prop

end AdequacyArchitecture.Adjudication
