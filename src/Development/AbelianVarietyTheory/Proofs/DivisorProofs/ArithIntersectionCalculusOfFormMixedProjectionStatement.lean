import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionCalculusOfFormMixedProjection
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithIntersectionCalculus_of_form_mixed_projection : GlobalTheory.Published.ArFormExists → GlobalTheory.Published.ArMix → GlobalTheory.Published.HeightProjection → GlobalTheory.Published.ArCalc := by
  first | exact @GlobalTheory.Published.arCalc_of_form_mix_projection | exact GlobalTheory.Published.arCalc_of_form_mix_projection | (intros; apply GlobalTheory.Published.arCalc_of_form_mix_projection <;> assumption)
