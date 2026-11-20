import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointIntegralityStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.point_integrality_statement : Hypotheses2 → HypothesesH → PtInt := by
  first | exact @GlobalTheory.HeightParts.ptInt | exact GlobalTheory.HeightParts.ptInt | (intros; apply GlobalTheory.HeightParts.ptInt <;> assumption)
