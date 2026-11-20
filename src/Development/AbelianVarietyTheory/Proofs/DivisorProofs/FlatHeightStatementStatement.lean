import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatHeightStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_height_statement : Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB → FlatHt := by
  first | exact @GlobalTheory.HeightParts.flatHt | exact GlobalTheory.HeightParts.flatHt | (intros; apply GlobalTheory.HeightParts.flatHt <;> assumption)
