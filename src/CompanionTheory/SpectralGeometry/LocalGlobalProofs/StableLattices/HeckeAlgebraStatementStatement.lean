import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeAlgebraStatement
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.HeckeAlgebraTheorem : StHecke := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBern.stHecke | exact GlobalTheory.CompanionTheory.HeckeBern.stHecke | (intros; apply GlobalTheory.CompanionTheory.HeckeBern.stHecke <;> assumption)
