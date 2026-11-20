import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoDetectedSubgroupTowerRatProof
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noDetectedSubgroupTowerRat_proof : NoTowerQ := by
  first | exact @GlobalTheory.PMon.Ram.noTowerQ_holds | exact GlobalTheory.PMon.Ram.noTowerQ_holds | (intros; apply GlobalTheory.PMon.Ram.noTowerQ_holds <;> assumption)
