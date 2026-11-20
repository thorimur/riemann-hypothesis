import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TruncatedDerivationLimit
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncated_derivation_limit : Factor → CutDer → CutLim := by
  first | exact @GlobalTheory.CompanionTheory.BesselCutLim.cutLim_of | exact GlobalTheory.CompanionTheory.BesselCutLim.cutLim_of | (intros; apply GlobalTheory.CompanionTheory.BesselCutLim.cutLim_of <;> assumption)
