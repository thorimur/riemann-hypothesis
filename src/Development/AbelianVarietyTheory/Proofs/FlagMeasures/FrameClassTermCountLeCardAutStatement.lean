import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameClassTermCountLeCardAut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameClass_termCount_le_card_aut : GlobalTheory.TypeAsm.FibCardC := by
  first | exact @GlobalTheory.TypeAsm.FibCard.fibCardC | exact GlobalTheory.TypeAsm.FibCard.fibCardC | (intros; apply GlobalTheory.TypeAsm.FibCard.fibCardC <;> assumption)
