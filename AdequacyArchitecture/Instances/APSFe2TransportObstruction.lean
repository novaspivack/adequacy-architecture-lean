/-
  **SPEC_029_FR1 — FE-2 (APS):** typed status — faithful APS discharge is a **middle** Strata layer, not an
  outer remainder-indexed summit certificate family.

  **Theorem-fed artifact.** `APSFaithful.lean` — `faithfulAPSCrossCorpusRealizationLayer` on **`Unit`**
  (`Middle.RealizationLayer Unit`).

  **FE-3 NEMS instance** packages **outer** phantom indices + `NEMSHaltingAnchoredSemanticReportCertificate`.
  A direct instantiation of **that** `IndexedPhantomCertificateOps` shape from `tracking` / `gluing` fields alone
  is not defined: the summit report type **`HaltingAnchoredGluedSummitSemanticReport`** is **NEMS-lawful**
  infrastructure, not a field projection of **`RealizationLayer`**.

  **Positive instance (FE-2+):** **`APSFe2MiddleTransport.lean`** — minimal **`Core`** with **`R := Prop`** and
  certificate **`M.ICompIdx`** on **`Middle.RealizationLayer Unit`** (incl. faithful cross-corpus).

  NEMS **`haltingAnchoredNems*`** reuse remains distinct: halting-anchored summit **report** types are not
  **`ICompIdx`** without a bespoke bridge.
-/

import AdequacyArchitecture.Instances.APSFaithful

namespace AdequacyArchitecture.Instances

/-- Mark for search: this definition is the concrete **theorem-fed `From*`** middle used in the joint / linked
stories — not interchangeable with **`haltingAnchoredNemsBranchGenericCore`** without a heterogeneous bridge. -/
abbrev apsFe2TheoremFedFromStar := faithfulAPSCrossCorpusRealizationLayer

end AdequacyArchitecture.Instances
