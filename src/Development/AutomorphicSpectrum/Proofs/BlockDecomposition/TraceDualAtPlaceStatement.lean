import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceDualAtPlace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_dual_at_place : PositivityTheory.SiegelWeilFormula.Gunr.TraceDualAt := by
  first | exact @GlobalTheory.CompanionTheory.Gunr.TraceDual.traceDualAt | exact GlobalTheory.CompanionTheory.Gunr.TraceDual.traceDualAt | (intros; apply GlobalTheory.CompanionTheory.Gunr.TraceDual.traceDualAt <;> assumption)
