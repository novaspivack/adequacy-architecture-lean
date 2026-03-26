/-
  Middle and inner hooks for the completed stratified class (SPEC_010 Phase B1).

  These are **typed slots** supplied by instances — not definition-level `Prop := True`.
  Middle: gluing compatibility + obstruction-at-site (APS / local–global spine).
  Inner: compare-relative residual signals on domain and codomain (Strata / WMF linkage).
-/

import AdequacyArchitecture.Core.Basic

universe u

namespace AdequacyArchitecture.Lawful

variable {α : Type u}

/-- Middle layer data: gluing-compatible transform/account pairs and obstruction witnesses.

`gluingObstructionAt` is indexed by burden site so it can be refined to a typed obstruction
without replacing the whole completed stratified structure. -/
structure LawfulMiddleLayer (α : Type u) where
  gluingCompatible (f : Transform α) (A : Account α) : Prop
  gluingObstructionAt (m : BurdenMode) (A : Account α) : Prop

/-- Inner layer data along a compare map `α → β`: residual signals on domain **accounts** and
codomain points.

Future work wires `codomainResidual` to Strata `rcsOfMap` / fundamental package; the slot is
here so `CompletedStratifiedLawfulAdequacyArchitecture` is not compare-only prose. -/
structure LawfulInnerHook (α : Type u) (β : Type u) where
  domainResidual (A : Account α) : Prop
  codomainResidual (b : β) : Prop

end AdequacyArchitecture.Lawful
