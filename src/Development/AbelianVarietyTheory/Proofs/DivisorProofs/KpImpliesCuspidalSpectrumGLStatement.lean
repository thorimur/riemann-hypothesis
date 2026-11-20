import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KpImpliesCuspidalSpectrumGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kp_implies_cuspidal_spectrum_GL : GlobalTheory.ThK.KP → GlobalTheory.Published.CuspidalSpectrumGL := by
  first | exact @GlobalTheory.ThK.cuspidalSpectrumGL_of_KP | exact GlobalTheory.ThK.cuspidalSpectrumGL_of_KP | (intros; apply GlobalTheory.ThK.cuspidalSpectrumGL_of_KP <;> assumption)
