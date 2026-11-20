import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_convergence_of_kernel : GlobalTheory.ThK.KP → GlobalTheory.ThK.WeilConv := by
  first | exact @GlobalTheory.ThKWeil.weilConv | exact GlobalTheory.ThKWeil.weilConv | (intros; apply GlobalTheory.ThKWeil.weilConv <;> assumption)
