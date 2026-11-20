import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightOfSizeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_of_size_bound : GlobalTheory.BigTop.Fun.SizeAt → GlobalTheory.BigTop.Fun.Wt @GlobalTheory.BigTop.Fun.Comparison₂ := by
  first | exact @GlobalTheory.BigTop.Fun.wt_tie | exact GlobalTheory.BigTop.Fun.wt_tie | (intros; apply GlobalTheory.BigTop.Fun.wt_tie <;> assumption)
