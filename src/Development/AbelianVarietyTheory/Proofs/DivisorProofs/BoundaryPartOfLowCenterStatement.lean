import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryPartOfLowCenter
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_part_of_low_center : LowSt → CentSt → OnObj fun _ _ _ T _ _ => ∀ c, GlobalTheory.RegEst.BdPart (T.F c) := by
  first | exact @GlobalTheory.RegBd.bdPart_of_low | exact GlobalTheory.RegBd.bdPart_of_low | (intros; apply GlobalTheory.RegBd.bdPart_of_low <;> assumption)
