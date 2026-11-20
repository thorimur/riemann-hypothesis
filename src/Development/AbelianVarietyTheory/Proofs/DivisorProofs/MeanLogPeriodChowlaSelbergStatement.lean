import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogPeriodChowlaSelberg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meanLogPeriod_chowlaSelberg : GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriod := by
  first | exact @GlobalTheory.MeanPeriodClosed.meanPeriod | exact GlobalTheory.MeanPeriodClosed.meanPeriod | (intros; apply GlobalTheory.MeanPeriodClosed.meanPeriod <;> assumption)
