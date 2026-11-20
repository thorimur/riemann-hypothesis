import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorGridScalarOfProjectorScalar
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projectorGridScalar_of_projectorScalar : GlobalTheory.LeviCut.StepScalar → GlobalTheory.LeviCut.GridScalar := by
  first | exact @GlobalTheory.LeviCut.gridScalar_of_stepScalar | exact GlobalTheory.LeviCut.gridScalar_of_stepScalar | (intros; apply GlobalTheory.LeviCut.gridScalar_of_stepScalar <;> assumption)
