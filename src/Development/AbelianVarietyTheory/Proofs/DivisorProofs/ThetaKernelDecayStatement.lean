import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelDecay
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_kernel_decay : GlobalTheory.ThK.KP → GlobalTheory.ThK.KDecay := by
  first | exact @GlobalTheory.KDecayProof.kDecay_of_classicalTheorems | exact GlobalTheory.KDecayProof.kDecay_of_classicalTheorems | (intros; apply GlobalTheory.KDecayProof.kDecay_of_classicalTheorems <;> assumption)
