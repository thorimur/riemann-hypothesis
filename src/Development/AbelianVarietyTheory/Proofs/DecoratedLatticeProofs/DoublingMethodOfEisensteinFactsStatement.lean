import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMethodOfEisensteinFacts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubling_method_of_eisenstein_facts : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.SiegelEisensteinSimplePole → GlobalTheory.Published.DoublingMethod := by
  first | exact @GlobalTheory.doublingMethod_of_three | exact GlobalTheory.doublingMethod_of_three | (intros; apply GlobalTheory.doublingMethod_of_three <;> assumption)
