import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ChartExistence
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ChartExistence : ChartExists := by
  first | exact @GlobalTheory.CompanionTheory.ProdExChart.chartExists | exact GlobalTheory.CompanionTheory.ProdExChart.chartExists | (intros; apply GlobalTheory.CompanionTheory.ProdExChart.chartExists <;> assumption)
