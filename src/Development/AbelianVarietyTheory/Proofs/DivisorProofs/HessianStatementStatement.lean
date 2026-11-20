import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessianStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hessian_statement : ConstSt → LowSt → HessSt := by
  first | exact @GlobalTheory.HessReg.hessSt | exact GlobalTheory.HessReg.hessSt | (intros; apply GlobalTheory.HessReg.hessSt <;> assumption)
