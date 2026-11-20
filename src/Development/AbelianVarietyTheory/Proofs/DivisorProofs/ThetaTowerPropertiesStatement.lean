import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTowerProperties
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_tower_properties : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.TowerA ∧ GlobalTheory.ThK.TowerB := by
  first | exact @GlobalTheory.ThK.towerA_and_towerB | exact GlobalTheory.ThK.towerA_and_towerB | (intros; apply GlobalTheory.ThK.towerA_and_towerB <;> assumption)
