import Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasureLimitStatementHolds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_limit_statement_holds : GroundTheory.Heights₂.Heights.LowerBoundFree.MuMeasureLimit.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.muMeasureLimit | exact GlobalTheory.CompanionTheory.Ar.Giv.muMeasureLimit | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.muMeasureLimit <;> assumption)
