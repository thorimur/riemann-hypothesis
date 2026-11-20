import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutantReductionReal
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutant_reduction_real : PositivityTheory.RgBcC.RealD.LeviCommutantWordReduction := by
  first | exact @GlobalTheory.CompanionTheory.BlockCapelliWords.commutant_block_capelli_words | exact GlobalTheory.CompanionTheory.BlockCapelliWords.commutant_block_capelli_words | (intros; apply GlobalTheory.CompanionTheory.BlockCapelliWords.commutant_block_capelli_words <;> assumption)
