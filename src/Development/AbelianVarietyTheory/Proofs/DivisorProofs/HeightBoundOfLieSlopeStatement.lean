import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightBoundOfLieSlope
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_bound_of_lie_slope : Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB → LieSlope → HtBdSt := by
  first | exact @GlobalTheory.HeightParts.BdHtProof.main | exact GlobalTheory.HeightParts.BdHtProof.main | (intros; apply GlobalTheory.HeightParts.BdHtProof.main <;> assumption)
