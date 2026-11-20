import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantTau

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.QuantumDeterminantTau : CompanionTheory.RgExh.Hk.QdetTau := by
  first | exact @GlobalTheory.CompanionTheory.CapelliTwist.qdetTau | exact GlobalTheory.CompanionTheory.CapelliTwist.qdetTau | (intros; apply GlobalTheory.CompanionTheory.CapelliTwist.qdetTau <;> assumption)
