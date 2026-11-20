import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerOfThetaMatching
open GlobalTheory.SqTop
theorem _root_.GlobalTheory.T.tower_of_theta_matching : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → LNe → Tower := by
  first | exact @GlobalTheory.SqTower.tower | exact GlobalTheory.SqTower.tower | (intros; apply GlobalTheory.SqTower.tower <;> assumption)
