import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHypothesesHold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_hypotheses_hold : PositivityTheory.Rg.BcB.G8.Fin.LocHyp := by
  first | exact @GlobalTheory.CompanionTheory.LocHypProof.locHyp | exact GlobalTheory.CompanionTheory.LocHypProof.locHyp | (intros; apply GlobalTheory.CompanionTheory.LocHypProof.locHyp <;> assumption)
