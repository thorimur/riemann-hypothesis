import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BranchProperAtPointHolds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.branch_proper_at_point_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BranchProperAtPoint.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Branch.branchProperAtPoint | exact GlobalTheory.CompanionTheory.Ar.Branch.branchProperAtPoint | (intros; apply GlobalTheory.CompanionTheory.Ar.Branch.branchProperAtPoint <;> assumption)
