import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomConstantOfTheta
open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_constant_of_theta : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → (∀ D, GlobalTheory.NormSum.Inp D) → BotSmall → LNe → BotConst := by
  first | exact @GlobalTheory.SqTop.botConst_of_inputs | exact GlobalTheory.SqTop.botConst_of_inputs | (intros; apply GlobalTheory.SqTop.botConst_of_inputs <;> assumption)
