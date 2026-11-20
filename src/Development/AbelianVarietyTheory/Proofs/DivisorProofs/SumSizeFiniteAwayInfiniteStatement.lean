import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumSizeFiniteAwayInfinite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_size_finite_away_infinite : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.SumSize.FinK ∧ GlobalTheory.SumSize.AwayK ∧ GlobalTheory.SumSize.InfK := by
  first | exact @GlobalTheory.SumSize.Join.fin_away_inf | exact GlobalTheory.SumSize.Join.fin_away_inf | (intros; apply GlobalTheory.SumSize.Join.fin_away_inf <;> assumption)
