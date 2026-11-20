import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoiceSizeNodes
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.explicitChoice_sizeNodes : SzRow (fun _ _ L => SizeNodes L) := by
  first | exact @GlobalTheory.EX.szRow_sizeNodes | exact GlobalTheory.EX.szRow_sizeNodes | (intros; apply GlobalTheory.EX.szRow_sizeNodes <;> assumption)
