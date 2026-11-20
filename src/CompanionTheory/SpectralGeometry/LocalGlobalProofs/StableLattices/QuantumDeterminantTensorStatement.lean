import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantTensor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.QuantumDeterminantTensor : CompanionTheory.RgExh.Hk.QdetTens := by
  first | exact @GlobalTheory.CompanionTheory.RgExh.qdetTens | exact GlobalTheory.CompanionTheory.RgExh.qdetTens | (intros; apply GlobalTheory.CompanionTheory.RgExh.qdetTens <;> assumption)
