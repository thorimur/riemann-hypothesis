import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradientStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gradient_statement : Hypotheses2 → HypothesesH → GradSt := by
  first | exact @GlobalTheory.GradFlag.gradSt | exact GlobalTheory.GradFlag.gradSt | (intros; apply GlobalTheory.GradFlag.gradSt <;> assumption)
