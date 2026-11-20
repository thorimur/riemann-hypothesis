import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DemaillyRegularisationEstimate
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.demailly_regularisation_estimate : Hypotheses2 → HypothesesH → GlobalTheory.Published.DemaillyRegularisation → RegSt := by
  first | exact @GlobalTheory.RegEst.regSt | exact GlobalTheory.RegEst.regSt | (intros; apply GlobalTheory.RegEst.regSt <;> assumption)
