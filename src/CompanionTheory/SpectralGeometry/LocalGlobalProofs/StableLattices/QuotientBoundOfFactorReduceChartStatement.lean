import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuotientBoundOfFactorReduceChart
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_bound_of_factor_reduce_chart : Factor → Reduce → ChartExists → QBound := by
  first | exact @GlobalTheory.CompanionTheory.BmuQBound.qBound | exact GlobalTheory.CompanionTheory.BmuQBound.qBound | (intros; apply GlobalTheory.CompanionTheory.BmuQBound.qBound <;> assumption)
