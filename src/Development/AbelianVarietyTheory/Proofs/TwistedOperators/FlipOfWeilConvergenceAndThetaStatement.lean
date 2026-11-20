import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlipOfWeilConvergenceAndTheta
open GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flip_of_weil_convergence_and_theta : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → ConstK → StepFlip := by
  first | exact @GlobalTheory.FlipRun.stepFlip_of | exact GlobalTheory.FlipRun.stepFlip_of | (intros; apply GlobalTheory.FlipRun.stepFlip_of <;> assumption)
