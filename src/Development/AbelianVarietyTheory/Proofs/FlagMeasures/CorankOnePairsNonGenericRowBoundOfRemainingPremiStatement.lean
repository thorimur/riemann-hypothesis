import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CorankOnePairsNonGenericRowBoundOfRemainingPremi
open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.corankOnePairsNonGenericRowBound_of_remaining_premises : StepChoiceConstantsC → StepPinExists → Formalism.L2.SG.NGVanish.FormNGC → StepThmBPinnedP → Formalism.L2.SG.FamDefs.OrbitFamilyIdentityNonGeneric → Formalism.L2.SG.FamDefs.WeightsNG → Formalism.L2.SG.FamDefs.ProductStructureNonGeneric → Formalism.L2.SG.FamDefs.ExistNG → RowNGP := by
  first | exact @GlobalTheory.rowNGP_of_leaves | exact GlobalTheory.rowNGP_of_leaves | (intros; apply GlobalTheory.rowNGP_of_leaves <;> assumption)
