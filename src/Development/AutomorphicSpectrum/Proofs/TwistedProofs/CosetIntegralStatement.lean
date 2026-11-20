import Development.AutomorphicSpectrum.Proofs.TwistedProofs.CosetIntegral
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetIntegral' : CosetIntegral := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.cosetIntegral | exact GlobalTheory.CompanionTheory.InertZeta.cosetIntegral | (intros; apply GlobalTheory.CompanionTheory.InertZeta.cosetIntegral <;> assumption)
