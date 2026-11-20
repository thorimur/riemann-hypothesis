import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_statement : KernelSt := by
  first | exact @GlobalTheory.HeightParts.kernelSt_holds | exact GlobalTheory.HeightParts.kernelSt_holds | (intros; apply GlobalTheory.HeightParts.kernelSt_holds <;> assumption)
