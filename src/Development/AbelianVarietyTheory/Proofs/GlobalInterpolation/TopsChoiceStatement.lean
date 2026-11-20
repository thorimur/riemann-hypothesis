import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TopsChoice
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tops_choice : TopsChoice := by
  first | exact @GlobalTheory.EX.exists_tops | exact GlobalTheory.EX.exists_tops | (intros; apply GlobalTheory.EX.exists_tops <;> assumption)
