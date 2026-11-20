import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanDecompositionGL
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.CartanDecompositionGL : StCartanGL := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.stCartanGL | exact GlobalTheory.CompanionTheory.CartGL.stCartanGL | (intros; apply GlobalTheory.CompanionTheory.CartGL.stCartanGL <;> assumption)
