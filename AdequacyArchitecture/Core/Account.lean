/-
  Accounts: representations over a target (predicates / observations).
-/

universe u

namespace AdequacyArchitecture

/-- An account over `α` is a unary predicate (first approximation of “theory over target”). -/
abbrev Account (α : Type u) := α → Prop

end AdequacyArchitecture
