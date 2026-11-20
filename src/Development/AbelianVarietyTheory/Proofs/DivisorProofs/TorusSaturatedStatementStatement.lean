import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusSaturatedStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_saturated_statement : Hypotheses2 → GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.TorusSaturated := by
  first | exact @GlobalTheory.TorusSat.main | exact GlobalTheory.TorusSat.main | (intros; apply GlobalTheory.TorusSat.main <;> assumption)
