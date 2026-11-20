import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfinitePairBounds
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_infinite_pair_bounds : GlobalTheory.FunPr.Hypotheses₂ → FinPairK ∧ InfPairK := by
  first | exact @GlobalTheory.FPair.main | exact GlobalTheory.FPair.main | (intros; apply GlobalTheory.FPair.main <;> assumption)
