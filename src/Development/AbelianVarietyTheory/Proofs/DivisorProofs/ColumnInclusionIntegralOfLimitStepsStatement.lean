import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnInclusionIntegralOfLimitSteps
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnInclusionIntegral_of_limitSteps : LimActSt → LimPtSt → LimFrameSt → InclSt := by
  first | exact @GlobalTheory.IsoTriv.Incl.inclSt_of_lim | exact GlobalTheory.IsoTriv.Incl.inclSt_of_lim | (intros; apply GlobalTheory.IsoTriv.Incl.inclSt_of_lim <;> assumption)
