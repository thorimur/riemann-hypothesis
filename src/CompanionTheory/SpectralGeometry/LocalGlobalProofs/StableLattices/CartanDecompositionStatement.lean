import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanDecomposition
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.CartanDecomposition : CartanQ := by
  first | exact @GlobalTheory.CompanionTheory.BesselCartan.cartanQ | exact GlobalTheory.CompanionTheory.BesselCartan.cartanQ | (intros; apply GlobalTheory.CompanionTheory.BesselCartan.cartanQ <;> assumption)
