import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chevalley_units : GlobalTheory.Published.ChevalleyUnits := by
  first | exact @GlobalTheory.Published.chevalleyUnits' | exact GlobalTheory.Published.chevalleyUnits' | (intros; apply GlobalTheory.Published.chevalleyUnits' <;> assumption)
