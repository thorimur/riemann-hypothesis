import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiPolarDecompositionEquivariance
open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_polar_decomposition_equivariance : PsiPolar := by
  first | exact @GlobalTheory.Dec.psiPolar | exact GlobalTheory.Dec.psiPolar | (intros; apply GlobalTheory.Dec.psiPolar <;> assumption)
