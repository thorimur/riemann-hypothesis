import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DerivedSeriesAdjoint
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.DerivedSeriesAdjoint : DsAd := by
  first | exact @GlobalTheory.CompanionTheory.BmuDsAd.dsAd | exact GlobalTheory.CompanionTheory.BmuDsAd.dsAd | (intros; apply GlobalTheory.CompanionTheory.BmuDsAd.dsAd <;> assumption)
