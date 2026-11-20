import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centre_statement : Hypotheses2 → HypothesesH → CentSt := by
  first | exact @GlobalTheory.CentFlat.centSt | exact GlobalTheory.CentFlat.centSt | (intros; apply GlobalTheory.CentFlat.centSt <;> assumption)
