import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistLevelStabiliserAtLevelPrimeProof
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof : GlobalTheory.AdForm.TwLev' := by
  first | exact @GlobalTheory.AdForm.twLev_prime | exact GlobalTheory.AdForm.twLev_prime | (intros; apply GlobalTheory.AdForm.twLev_prime <;> assumption)
