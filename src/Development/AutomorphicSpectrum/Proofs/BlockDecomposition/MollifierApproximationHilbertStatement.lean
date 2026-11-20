import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MollifierApproximationHilbert

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mollifier_approximation_hilbert : PositivityTheory.RgDs.Hilb.StepMoll := by
  first | exact @GlobalTheory.CompanionTheory.HilbMoll.stepMoll | exact GlobalTheory.CompanionTheory.HilbMoll.stepMoll | (intros; apply GlobalTheory.CompanionTheory.HilbMoll.stepMoll <;> assumption)
