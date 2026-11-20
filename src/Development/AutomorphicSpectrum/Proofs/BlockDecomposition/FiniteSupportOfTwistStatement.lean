import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportOfTwist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_support_of_twist : PositivityTheory.Rg.BcB.G8.Fin.SuppFinOf := by
  first | exact @GlobalTheory.CompanionTheory.SuppFinTw.suppFinOf | exact GlobalTheory.CompanionTheory.SuppFinTw.suppFinOf | (intros; apply GlobalTheory.CompanionTheory.SuppFinTw.suppFinOf <;> assumption)
