import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmValuesMinPadicValBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedPowerValuations_minVal : Formalism.PairingDivisionLocalBalance.MinVal := by
  first | exact @GlobalTheory.cmValues_minPadicVal_bound | exact GlobalTheory.cmValues_minPadicVal_bound | (intros; apply GlobalTheory.cmValues_minPadicVal_bound <;> assumption)
