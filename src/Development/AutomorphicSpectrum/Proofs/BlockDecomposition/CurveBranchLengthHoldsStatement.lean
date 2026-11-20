import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CurveBranchLengthHolds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_branch_length_holds : GroundTheory.Heights₂.Heights.CurveBranchLength.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Heights.CurveBranch.curveBranchLength | exact GlobalTheory.CompanionTheory.Heights.CurveBranch.curveBranchLength | (intros; apply GlobalTheory.CompanionTheory.Heights.CurveBranch.curveBranchLength <;> assumption)
