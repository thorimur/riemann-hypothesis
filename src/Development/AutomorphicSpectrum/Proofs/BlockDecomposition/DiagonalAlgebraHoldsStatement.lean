import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalAlgebraHolds
open PositivityTheory.Rg.BcB.F.Eig
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_algebra_holds : DiagAlg := by
  first | exact @GlobalTheory.CompanionTheory.BlockScalars.diagAlg | exact GlobalTheory.CompanionTheory.BlockScalars.diagAlg | (intros; apply GlobalTheory.CompanionTheory.BlockScalars.diagAlg <;> assumption)
