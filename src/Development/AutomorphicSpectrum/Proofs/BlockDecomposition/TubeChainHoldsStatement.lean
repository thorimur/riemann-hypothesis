import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TubeChainHolds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tube_chain_holds : PositivityTheory.RgEis.TubeChain := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.tubeChain | exact GlobalTheory.CompanionTheory.TubeFourier.tubeChain | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.tubeChain <;> assumption)
