import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneTorusClassNumberBoundProof
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normOneTorusClassNumberBound_proof : GlobalTheory.UCls.TorusBound := by
  first | exact @GlobalTheory.UCls.torusBound | exact GlobalTheory.UCls.torusBound | (intros; apply GlobalTheory.UCls.torusBound <;> assumption)
