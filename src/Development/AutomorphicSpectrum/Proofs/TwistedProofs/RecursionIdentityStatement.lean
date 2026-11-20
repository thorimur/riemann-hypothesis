import Development.AutomorphicSpectrum.Proofs.TwistedProofs.RecursionIdentity
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.recursion_identity : Step := by
  first | exact @GlobalTheory.CompanionTheory.InertLevi.step | exact GlobalTheory.CompanionTheory.InertLevi.step | (intros; apply GlobalTheory.CompanionTheory.InertLevi.step <;> assumption)
