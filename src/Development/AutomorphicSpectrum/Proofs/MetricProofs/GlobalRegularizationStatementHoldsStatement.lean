import Development.AutomorphicSpectrum.Proofs.MetricProofs.GlobalRegularizationStatementHolds
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_regularization_statement_holds : RegGlobalStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.regGlobalStatement_holds | exact GlobalTheory.CompanionTheory.Ar.Giv.regGlobalStatement_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.regGlobalStatement_holds <;> assumption)
