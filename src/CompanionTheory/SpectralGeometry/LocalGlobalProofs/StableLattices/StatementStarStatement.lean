import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StatementStar
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.StatementStar : StStar := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.StarPf.stStar | exact GlobalTheory.CompanionTheory.RgFl.StarPf.stStar | (intros; apply GlobalTheory.CompanionTheory.RgFl.StarPf.stStar <;> assumption)
