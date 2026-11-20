import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsHeisenbergTranslationLaw
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatMaps_heisenbergTranslation_law : ∀ D : D7, GlobalTheory.FinPl.FlatShift D := by
  first | exact @GlobalTheory.FlatShiftPf.flatShift | exact GlobalTheory.FlatShiftPf.flatShift | (intros; apply GlobalTheory.FlatShiftPf.flatShift <;> assumption)
