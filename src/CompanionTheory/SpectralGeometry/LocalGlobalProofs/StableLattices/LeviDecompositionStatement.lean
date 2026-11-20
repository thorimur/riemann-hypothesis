import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviDecomposition
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.LeviDecomposition : LeviQ := by
  first | exact @GlobalTheory.CompanionTheory.BesselLevi.leviQ | exact GlobalTheory.CompanionTheory.BesselLevi.leviQ | (intros; apply GlobalTheory.CompanionTheory.BesselLevi.leviQ <;> assumption)
