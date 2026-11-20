import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GapHypothesisOfLargenessConstantGe
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gapC_holds : GlobalTheory.TypeAsm.GapC := by
  first | exact @GlobalTheory.TypeAsm.gapC | exact GlobalTheory.TypeAsm.gapC | (intros; apply GlobalTheory.TypeAsm.gapC <;> assumption)
