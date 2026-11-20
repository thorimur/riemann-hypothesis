import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThinChoiceOfZeroDensity
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thin_choice_of_zero_density : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → ThinChoice := by
  first | exact @GlobalTheory.EX.thinChoice_of_explicit | exact GlobalTheory.EX.thinChoice_of_explicit | (intros; apply GlobalTheory.EX.thinChoice_of_explicit <;> assumption)
