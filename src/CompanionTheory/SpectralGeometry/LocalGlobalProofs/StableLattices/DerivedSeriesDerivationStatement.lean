import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DerivedSeriesDerivation
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.DerivedSeriesDerivation : DsDer := by
  first | exact @GlobalTheory.CompanionTheory.BmuDsDer.dsDer | exact GlobalTheory.CompanionTheory.BmuDsDer.dsDer | (intros; apply GlobalTheory.CompanionTheory.BmuDsDer.dsDer <;> assumption)
