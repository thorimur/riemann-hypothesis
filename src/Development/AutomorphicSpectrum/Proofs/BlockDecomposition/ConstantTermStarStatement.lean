import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_star : PositivityTheory.Rg.BcB.F.MLM.CtStar := by
  first | exact @GlobalTheory.CompanionTheory.CtAdj.ctStar | exact GlobalTheory.CompanionTheory.CtAdj.ctStar | (intros; apply GlobalTheory.CompanionTheory.CtAdj.ctStar <;> assumption)
