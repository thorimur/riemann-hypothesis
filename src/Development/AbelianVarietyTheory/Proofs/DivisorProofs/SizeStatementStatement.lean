import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.size_statement : Hypotheses2 → HypothesesH → SizeSt := by
  first | exact @GlobalTheory.HomWtBd.sizeSt | exact GlobalTheory.HomWtBd.sizeSt | (intros; apply GlobalTheory.HomWtBd.sizeSt <;> assumption)
