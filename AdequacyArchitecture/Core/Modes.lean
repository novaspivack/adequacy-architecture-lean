/-
  Adequacy Architecture — typed adequacy and burden modes (program ontology).
-/

namespace AdequacyArchitecture

/-- Adequacy *mode*: which sense of “adequate account” is at issue. -/
inductive AdeqMode : Type
  | repr | cert | obs | route | cont | final
  deriving DecidableEq, Repr

/-- Burden *mode*: which kind of structured load is tracked. -/
inductive BurdenMode : Type
  | sem | sel | res | glue | cont | route
  deriving DecidableEq, Repr

/-- Tags for canonical carrier families (residual kernel, gluing, etc.). -/
inductive CarrierTag : Type
  | residual | gluingObstruction | adjudicative | boundaryDefect | routeComplexity | semanticRemainder
  deriving DecidableEq, Repr

end AdequacyArchitecture
