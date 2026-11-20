import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixLengthExistsOfElementaryDivisors
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixLengthExists_of_elementaryDivisors : Smith → FracExists := by
  first | exact @GlobalTheory.InertZeta.fracExists_of_smith | exact GlobalTheory.InertZeta.fracExists_of_smith | (intros; apply GlobalTheory.InertZeta.fracExists_of_smith <;> assumption)
