import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FixedVectorStatement
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.FixedVectorStatement : StFixVec := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.stFixVec | exact GlobalTheory.CompanionTheory.RgFl.stFixVec | (intros; apply GlobalTheory.CompanionTheory.RgFl.stFixVec <;> assumption)
