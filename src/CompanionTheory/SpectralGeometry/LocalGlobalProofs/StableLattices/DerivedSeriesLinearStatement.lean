import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DerivedSeriesLinear
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.DerivedSeriesLinear : DsLin := by
  first | exact @GlobalTheory.CompanionTheory.BesselMapSm.dsLin | exact GlobalTheory.CompanionTheory.BesselMapSm.dsLin | (intros; apply GlobalTheory.CompanionTheory.BesselMapSm.dsLin <;> assumption)
