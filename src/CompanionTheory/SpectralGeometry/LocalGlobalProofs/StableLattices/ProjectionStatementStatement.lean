import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ProjectionStatement
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ProjectionStatement : StProj := by
  first | exact @GlobalTheory.CompanionTheory.FixedProj.stProj | exact GlobalTheory.CompanionTheory.FixedProj.stProj | (intros; apply GlobalTheory.CompanionTheory.FixedProj.stProj <;> assumption)
