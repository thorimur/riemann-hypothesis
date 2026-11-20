import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CutEffectiveDivisor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cut_effective_divisor : GroundTheory.Heights₂.Heights.NumbersDVR.CutByEffectiveDivisor.Statement.{0} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.CutClosed.main | exact GlobalTheory.CompanionTheory.Ar.Num.CutClosed.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.CutClosed.main <;> assumption)
