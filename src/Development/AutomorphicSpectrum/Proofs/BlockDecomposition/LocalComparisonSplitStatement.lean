import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_comparison_split : PositivityTheory.Rg.BcB.G8.Fin.LocCompareSplit := by
  first | exact @GlobalTheory.CompanionTheory.LcSplit.locCompareSplit | exact GlobalTheory.CompanionTheory.LcSplit.locCompareSplit | (intros; apply GlobalTheory.CompanionTheory.LcSplit.locCompareSplit <;> assumption)
