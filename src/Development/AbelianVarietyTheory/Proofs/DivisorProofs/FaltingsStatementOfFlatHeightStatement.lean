import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaltingsStatementOfFlatHeight
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.faltings_statement_of_flat_height : Hypotheses2 → HypothesesH → FlatHt → FaltSt := by
  first | exact @GlobalTheory.HalfFalt.faltSt | exact GlobalTheory.HalfFalt.faltSt | (intros; apply GlobalTheory.HalfFalt.faltSt <;> assumption)
