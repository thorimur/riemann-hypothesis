import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastSeesawLinearLeftLargeDepth
open GlobalTheory.RowClaim GlobalTheory.ConnectionLinear
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastSeesaw_linear_left_largeDepth : Big fun ch => GlobalTheory.ConnectionLinear.LastLin ch 0 := by
  first | exact @GlobalTheory.LastPositionLin.lastLin_zero | exact GlobalTheory.LastPositionLin.lastLin_zero | (intros; apply GlobalTheory.LastPositionLin.lastLin_zero <;> assumption)
