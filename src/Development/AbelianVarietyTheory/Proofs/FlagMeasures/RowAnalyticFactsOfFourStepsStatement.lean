import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowAnalyticFactsOfFourSteps
open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowAnalyticFacts_of_four_steps : StepPinExists → StepVanishPinned → StepLocGenPinnedC → StepThmBPinnedP → StepAnalyticP := by
  first | exact @GlobalTheory.NGRow.stepAnalyticP_of_steps | exact GlobalTheory.NGRow.stepAnalyticP_of_steps | (intros; apply GlobalTheory.NGRow.stepAnalyticP_of_steps <;> assumption)
