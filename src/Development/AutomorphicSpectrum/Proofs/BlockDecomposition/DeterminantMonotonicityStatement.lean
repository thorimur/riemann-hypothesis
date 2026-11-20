import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeterminantMonotonicity
open Matrix PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_monotonicity : DetMono := by
  first | exact @GlobalTheory.CompanionTheory.DetMonotone.detMono | exact GlobalTheory.CompanionTheory.DetMonotone.detMono | (intros; apply GlobalTheory.CompanionTheory.DetMonotone.detMono <;> assumption)
