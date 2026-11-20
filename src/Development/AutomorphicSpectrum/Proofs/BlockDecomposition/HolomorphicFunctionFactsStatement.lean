import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicFunctionFacts

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_function_facts : PositivityTheory.RgDs.K.HolFacts := by
  first | exact @GlobalTheory.CompanionTheory.HolOm.holFacts | exact GlobalTheory.CompanionTheory.HolOm.holFacts | (intros; apply GlobalTheory.CompanionTheory.HolOm.holFacts <;> assumption)
