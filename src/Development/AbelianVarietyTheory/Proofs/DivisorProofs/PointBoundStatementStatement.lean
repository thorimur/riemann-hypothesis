import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointBoundStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.point_bound_statement : Hypotheses2 → HypothesesH → GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.TorusSaturated → PtBd := by
  first | exact @GlobalTheory.HeightParts.ptBd_holds | exact GlobalTheory.HeightParts.ptBd_holds | (intros; apply GlobalTheory.HeightParts.ptBd_holds <;> assumption)
