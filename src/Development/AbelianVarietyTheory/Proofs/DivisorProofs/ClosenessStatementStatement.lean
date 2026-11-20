import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosenessStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closeness_statement : Hypotheses2 → HypothesesH → KernelSt → GradSt → CloseSt := by
  first | exact @GlobalTheory.CloseReg.closeSt | exact GlobalTheory.CloseReg.closeSt | (intros; apply GlobalTheory.CloseReg.closeSt <;> assumption)
