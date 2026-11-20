import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralsOfMinguez
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_integrals_of_minguez : GlobalTheory.Published.MinguezThetaGL → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree := by
  first | exact @GlobalTheory.SquareAgree.thetaIntegralsAgree | exact GlobalTheory.SquareAgree.thetaIntegralsAgree | (intros; apply GlobalTheory.SquareAgree.thetaIntegralsAgree <;> assumption)
