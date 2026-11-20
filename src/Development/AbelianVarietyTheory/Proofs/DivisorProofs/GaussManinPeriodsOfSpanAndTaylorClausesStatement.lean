import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussManinPeriodsOfSpanAndTaylorClauses
open GlobalTheory.AnPer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussManinPeriods_of_span_and_taylor_clauses : PSpan → PTaylor → GlobalTheory.Published.GaussManinPeriods := by
  first | exact @GlobalTheory.AnPer.gaussManinPeriods_of_span_taylor | exact GlobalTheory.AnPer.gaussManinPeriods_of_span_taylor | (intros; apply GlobalTheory.AnPer.gaussManinPeriods_of_span_taylor <;> assumption)
