/-
  SPEC_019_CE8 — **Corpus elevation chain** as an ordered checklist (mirrors
  `SPEC_CORPUS_DISCHARGE_NEXT_STEPS.md` and `SPEC_013`).
-/

namespace AdequacyArchitecture.Instances

/-- Ordered phases for corpus elevation (advisor checklist; no proof obligations). -/
inductive CorpusElevationPhase where
  | frameworkCarrier
  | instantiateFromStar
  | mapToLawful
  | dischargeBottleneckRidge
  | documentArtifact

end AdequacyArchitecture.Instances
