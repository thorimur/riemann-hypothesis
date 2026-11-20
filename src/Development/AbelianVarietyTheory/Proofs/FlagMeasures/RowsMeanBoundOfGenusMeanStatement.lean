import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsMeanBoundOfGenusMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowsMeanC_holds : GlobalTheory.TypeAsm.RowsMeanC := by
  first | exact @GlobalTheory.TypeAsm.rowsMean | exact GlobalTheory.TypeAsm.rowsMean | (intros; apply GlobalTheory.TypeAsm.rowsMean <;> assumption)
