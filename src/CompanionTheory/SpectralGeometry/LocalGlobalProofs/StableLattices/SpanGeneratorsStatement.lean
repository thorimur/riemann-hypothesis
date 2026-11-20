import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SpanGenerators
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.SpanGenerators : SpanG := by
  first | exact @GlobalTheory.CompanionTheory.BmuSpan.spanG | exact GlobalTheory.CompanionTheory.BmuSpan.spanG | (intros; apply GlobalTheory.CompanionTheory.BmuSpan.spanG <;> assumption)
