import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleExistenceOfTheta
open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_existence_of_theta : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → LNe → TriEx := by
  first | exact @GlobalTheory.SqTop.triEx_holds | exact GlobalTheory.SqTop.triEx_holds | (intros; apply GlobalTheory.SqTop.triEx_holds <;> assumption)
