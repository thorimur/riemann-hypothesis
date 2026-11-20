import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePartOfHessianCenter
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curvature_part_of_hessian_center : HessSt → CentSt → OnObj fun _ _ _ T _ _ => ∀ c, GlobalTheory.RegEst.CurvPart (T.F c) := by
  first | exact @GlobalTheory.RegCurv.curvPart | exact GlobalTheory.RegCurv.curvPart | (intros; apply GlobalTheory.RegCurv.curvPart <;> assumption)
