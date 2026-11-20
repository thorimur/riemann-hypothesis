import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistTranslationsActAtLevelPrimeProof
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistTranslationsActAtLevelPrime_proof : GlobalTheory.AdForm.TwTrans' := by
  first | exact @GlobalTheory.AdForm.TransAct.twTransAct | exact GlobalTheory.AdForm.TransAct.twTransAct | (intros; apply GlobalTheory.AdForm.TransAct.twTransAct <;> assumption)
