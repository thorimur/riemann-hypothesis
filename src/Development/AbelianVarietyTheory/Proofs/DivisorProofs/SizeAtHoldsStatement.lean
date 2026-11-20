import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeAtHolds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.size_at_holds : GlobalTheory.BigTop.Fun.SizeAt := by
  first | exact @GlobalTheory.BigTop.Fun.SizeProof.sizeAt | exact GlobalTheory.BigTop.Fun.SizeProof.sizeAt | (intros; apply GlobalTheory.BigTop.Fun.SizeProof.sizeAt <;> assumption)
