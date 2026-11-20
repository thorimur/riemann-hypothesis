import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosePartOfSizeLowClose
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.close_part_of_size_low_close : SizeSt → LowSt → CloseSt → OnObj fun _ _ _ T _ _ => ∀ c, GlobalTheory.RegEst.ClosePart (T.F c) := by
  first | exact @GlobalTheory.RegEst.closePart_of_steps | exact GlobalTheory.RegEst.closePart_of_steps | (intros; apply GlobalTheory.RegEst.closePart_of_steps <;> assumption)
