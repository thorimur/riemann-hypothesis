import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFlagBundlePushForwardFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullFlagBundle_pushForward_formula : GlobalTheory.Published.FlagPushForward := by
  first | exact @GlobalTheory.FlagPushProof.flagPushForward | exact GlobalTheory.FlagPushProof.flagPushForward | (intros; apply GlobalTheory.FlagPushProof.flagPushForward <;> assumption)
