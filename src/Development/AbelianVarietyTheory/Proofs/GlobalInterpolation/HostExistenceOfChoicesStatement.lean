import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HostExistenceOfChoices
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.host_existence_of_choices : QDChoice → ThinChoice → NormPrimes → SmallPrimeOne → TopsChoice → HostEx := by
  first | exact @GlobalTheory.EX.HostExist.hostEx | exact GlobalTheory.EX.HostExist.hostEx | (intros; apply GlobalTheory.EX.HostExist.hostEx <;> assumption)
