import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CohomologicalCsdTemperedOfSegments
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomological_csd_tempered_of_segments : GlobalTheory.Published.CaraianiTempered → GlobalTheory.Published.TemperedProductOfSquareIntegrable → GlobalTheory.Published.EssSquareIntegrableSegments → GlobalTheory.Published.CohomologicalCsdTempered := by
  first | exact @GlobalTheory.Published.cohomologicalCsdTempered_of_caraianiTempered | exact GlobalTheory.Published.cohomologicalCsdTempered_of_caraianiTempered | (intros; apply GlobalTheory.Published.cohomologicalCsdTempered_of_caraianiTempered <;> assumption)
