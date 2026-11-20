import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityAtFittedPoints
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicity_at_fitted_points : GlobalTheory.BigTop.Fun.SetAt → GlobalTheory.BigTop.Fun.MM @GlobalTheory.BigTop.Fun.Comparison₂ := by
  first | exact @GlobalTheory.BigTop.Fun.LeafMMTie.mm_tie | exact GlobalTheory.BigTop.Fun.LeafMMTie.mm_tie | (intros; apply GlobalTheory.BigTop.Fun.LeafMMTie.mm_tie <;> assumption)
