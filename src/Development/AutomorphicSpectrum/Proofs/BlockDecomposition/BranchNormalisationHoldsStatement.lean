import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BranchNormalisationHolds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.branch_normalisation_holds : GroundTheory.Heights₂.Heights.BranchNormalisation.Statement := by
  first | exact @GlobalTheory.CompanionTheory.BranchNorm.branchNormalisation | exact GlobalTheory.CompanionTheory.BranchNorm.branchNormalisation | (intros; apply GlobalTheory.CompanionTheory.BranchNorm.branchNormalisation <;> assumption)
