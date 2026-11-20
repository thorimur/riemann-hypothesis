import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjectionOfFunctorialityAdopted
open GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projection_of_functoriality_adopted : GlobalTheory.FunPr.Hypotheses₂ → StepProj := by
  first | exact @GlobalTheory.Adopt.projection_of_functoriality_adopted | exact GlobalTheory.Adopt.projection_of_functoriality_adopted | (intros; apply GlobalTheory.Adopt.projection_of_functoriality_adopted <;> assumption)
