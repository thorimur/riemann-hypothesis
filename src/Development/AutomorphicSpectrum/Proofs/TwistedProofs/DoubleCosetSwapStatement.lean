import Development.AutomorphicSpectrum.Proofs.TwistedProofs.DoubleCosetSwap
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_coset_swap : DosetSwap := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.dosetSwap | exact GlobalTheory.CompanionTheory.InertZeta.dosetSwap | (intros; apply GlobalTheory.CompanionTheory.InertZeta.dosetSwap <;> assumption)
