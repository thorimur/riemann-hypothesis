import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwasawaDecomposition
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.IwasawaDecomposition : IwaQ := by
  first | exact @GlobalTheory.CompanionTheory.BmuIwa.iwaQ | exact GlobalTheory.CompanionTheory.BmuIwa.iwaQ | (intros; apply GlobalTheory.CompanionTheory.BmuIwa.iwaQ <;> assumption)
