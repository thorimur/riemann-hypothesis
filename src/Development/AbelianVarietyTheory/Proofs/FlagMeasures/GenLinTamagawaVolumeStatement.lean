import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenLinTamagawaVolume
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genLin_tamagawa_volume : GenLinVolume := by
  first | exact @GlobalTheory.FlagMeas.genLinVolume | exact GlobalTheory.FlagMeas.genLinVolume | (intros; apply GlobalTheory.FlagMeas.genLinVolume <;> assumption)
