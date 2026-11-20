import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorsOfSmoothThetaStable
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomialVectors_of_smoothTheta_stable : ∀ D : D7, Formalism.IndefR.Fin.PtStable D := by
  first | exact @GlobalTheory.FockTheta.ptStable | exact GlobalTheory.FockTheta.ptStable | (intros; apply GlobalTheory.FockTheta.ptStable <;> assumption)
