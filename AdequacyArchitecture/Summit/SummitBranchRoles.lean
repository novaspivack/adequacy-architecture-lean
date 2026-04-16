/-
  Phase 3 — role-aware summit contract.

  Minimal **named roles** for a future refactor of **`FinalConditionalSummit.HFinal`** (or parallel packaging):
  branches that enter the adequacy law via **relocation/finality** vs **composition/gluing/obstruction**.

  **Wiring:** use **`AdequacyArchitecture.Lawful.FinalConditionalSummit.HFinalWithBranchRole`** (same `HFinal` payload
  + role tag). Tags are metadata; **`highestReachable_summit_at`** still uses **`toHFinal`** only.
-/

namespace AdequacyArchitecture.Summit

/-- Admissible branch roles for three-branch closure (minimal). -/
inductive SummitBranchRole : Type
  /-- NEMS-style spine: burden relocation + finality / route profile on a **rich** carrier (e.g. corpus `Fin 2`). -/
  | relocationFinality
  /-- IC-style native-vs-represented certification and outer-closure data **alongside** a corpus `HFinal`
  (same Layer-A payload may be tagged either this or **`relocationFinality`** depending on branch story). -/
  | certificationRepresentation
  /-- APS-style middle: tracking, gluing, interpolation, composition obstructions. -/
  | compositionGluing

end AdequacyArchitecture.Summit
