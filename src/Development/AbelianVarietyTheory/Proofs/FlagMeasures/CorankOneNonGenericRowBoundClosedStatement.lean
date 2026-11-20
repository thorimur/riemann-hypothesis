import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CorankOneNonGenericRowBoundClosed
open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.corankOneNonGenericRowBound_closed : PI.VolStabS.MassDataS.SWXS → StepChoiceConstantsC → StepPinExists → Formalism.L2.SG.NGVanish.FormNGC → StepThmBPinnedP → RowNGP := by
  first | exact @GlobalTheory.NGRowClose.close | exact GlobalTheory.NGRowClose.close | (intros; apply GlobalTheory.NGRowClose.close <;> assumption)
