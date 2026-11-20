import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryRankLeOneIntegralPoints
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_rank_le_one_integral_points : SmallRank := by
  first | exact @GlobalTheory.InertZeta.smallRank | exact GlobalTheory.InertZeta.smallRank | (intros; apply GlobalTheory.InertZeta.smallRank <;> assumption)
