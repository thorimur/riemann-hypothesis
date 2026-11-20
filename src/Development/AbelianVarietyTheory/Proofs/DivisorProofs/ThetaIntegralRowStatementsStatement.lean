import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralRowStatements
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_integral_row_statements : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.RowClaim.SumOKK ∧ GlobalTheory.RowClaim.ConstK ∧ GlobalTheory.RowClaim.LinK ∧ GlobalTheory.RowClaim.Formula2K ∧ GlobalTheory.RowClaim.SumRatK := by
  first | exact @GlobalTheory.RowClaim.JoinF.claims | exact GlobalTheory.RowClaim.JoinF.claims | (intros; apply GlobalTheory.RowClaim.JoinF.claims <;> assumption)
