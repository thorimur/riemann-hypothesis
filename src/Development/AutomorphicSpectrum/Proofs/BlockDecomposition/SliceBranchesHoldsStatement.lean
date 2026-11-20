import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceBranchesHolds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slice_branches_holds : GroundTheory.Heights₂.Heights.SliceBranches.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SliceBranch.sliceBranches | exact GlobalTheory.CompanionTheory.Ar.SliceBranch.sliceBranches | (intros; apply GlobalTheory.CompanionTheory.Ar.SliceBranch.sliceBranches <;> assumption)
