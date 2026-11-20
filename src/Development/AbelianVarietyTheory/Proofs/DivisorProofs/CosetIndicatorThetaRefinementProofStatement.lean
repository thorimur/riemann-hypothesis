import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetIndicatorThetaRefinementProof
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetIndicatorThetaRefinement_proof : GlobalTheory.ColNorms.CosetRefinement := by
  first | exact @GlobalTheory.ColNorms.coset_refinement | exact GlobalTheory.ColNorms.coset_refinement | (intros; apply GlobalTheory.ColNorms.coset_refinement <;> assumption)
