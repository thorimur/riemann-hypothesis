import Development.AutomorphicSpectrum.Proofs.TwistedProofs.SmallRankBound
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_rank_bound : SmallRank := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.smallRank | exact GlobalTheory.CompanionTheory.InertZeta.smallRank | (intros; apply GlobalTheory.CompanionTheory.InertZeta.smallRank <;> assumption)
