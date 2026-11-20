import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineEqDeRhamOfSmoothLiftComparison
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_eq_deRham_of_smoothLift_comparison : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.CrystallineDeRham := by
  first | exact @GlobalTheory.CrysLift.crystallineDeRham_of_smoothLift | exact GlobalTheory.CrysLift.crystallineDeRham_of_smoothLift | (intros; apply GlobalTheory.CrysLift.crystallineDeRham_of_smoothLift <;> assumption)
