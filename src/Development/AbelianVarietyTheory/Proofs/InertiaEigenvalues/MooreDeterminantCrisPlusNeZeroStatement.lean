import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MooreDeterminantCrisPlusNeZero
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mooreDeterminant_crisPlus_ne_zero : Moore := by
  first | exact @GlobalTheory.PMon.moore_statement | exact GlobalTheory.PMon.moore_statement | (intros; apply GlobalTheory.PMon.moore_statement <;> assumption)
