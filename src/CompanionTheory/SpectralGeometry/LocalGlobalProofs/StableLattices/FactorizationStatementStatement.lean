import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FactorizationStatement
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.FactorizationStatement : StFactor := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.stFactor | exact GlobalTheory.CompanionTheory.RgFl.stFactor | (intros; apply GlobalTheory.CompanionTheory.RgFl.stFactor <;> assumption)
