import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentCovolumeFiniteBounded
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralUnipotent_covolume_finite_bounded : GlobalTheory.TypeAsm.CovNC := by
  first | exact @GlobalTheory.TypeAsm.covNC_holds | exact GlobalTheory.TypeAsm.covNC_holds | (intros; apply GlobalTheory.TypeAsm.covNC_holds <;> assumption)
