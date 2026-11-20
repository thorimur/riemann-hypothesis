import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MovingStatement
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.MovingStatement : StMove := by
  first | exact @GlobalTheory.CompanionTheory.CartanMove.stMove | exact GlobalTheory.CompanionTheory.CartanMove.stMove | (intros; apply GlobalTheory.CompanionTheory.CartanMove.stMove <;> assumption)
