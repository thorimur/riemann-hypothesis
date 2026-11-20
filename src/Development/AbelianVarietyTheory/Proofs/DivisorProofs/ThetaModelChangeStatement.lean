import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelChange
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_model_change : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.ModelChange := by
  first | exact @GlobalTheory.ModelChg.modelChange | exact GlobalTheory.ModelChg.modelChange | (intros; apply GlobalTheory.ModelChg.modelChange <;> assumption)
