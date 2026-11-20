import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleTensorCommutant
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularSemisimple_tensor_commutant : GlobalTheory.RegSS.PointsCommutant := by
  first | exact @GlobalTheory.RegSS.pointsCommutant | exact GlobalTheory.RegSS.pointsCommutant | (intros; apply GlobalTheory.RegSS.pointsCommutant <;> assumption)
