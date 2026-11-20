import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleTensorInvolutionAdjoint
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularSemisimple_tensor_involution_adjoint : GlobalTheory.RegSS.PointsAdjoint := by
  first | exact @GlobalTheory.RegSS.pointsAdjoint | exact GlobalTheory.RegSS.pointsAdjoint | (intros; apply GlobalTheory.RegSS.pointsAdjoint <;> assumption)
