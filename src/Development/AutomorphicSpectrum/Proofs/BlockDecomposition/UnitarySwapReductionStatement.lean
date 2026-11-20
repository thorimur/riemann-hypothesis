import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitarySwapReduction
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_swap_reduction : PositivityTheory.SphericalProduct.SwapStepU := by
  first | exact @GlobalTheory.CompanionTheory.SwapRoot.swapStepU | exact GlobalTheory.CompanionTheory.SwapRoot.swapStepU | (intros; apply GlobalTheory.CompanionTheory.SwapRoot.swapStepU <;> assumption)
