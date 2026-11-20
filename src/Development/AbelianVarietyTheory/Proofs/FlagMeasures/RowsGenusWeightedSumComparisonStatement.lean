import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsGenusWeightedSumComparison
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowsGenus_weightedSumComparison : GlobalTheory.TypeAsm.RowsOrbC := by
  first | exact @GlobalTheory.RowsOrb.rowsOrbC | exact GlobalTheory.RowsOrb.rowsOrbC | (intros; apply GlobalTheory.RowsOrb.rowsOrbC <;> assumption)
