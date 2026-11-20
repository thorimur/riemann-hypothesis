import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOfSumBound
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depth_of_sum_bound : GlobalTheory.FunPr.Hypotheses₂ → SumOKK → DepthK := by
  first | exact @GlobalTheory.DepthUnf.depthK_of_sumOKK₂ | exact GlobalTheory.DepthUnf.depthK_of_sumOKK₂ | (intros; apply GlobalTheory.DepthUnf.depthK_of_sumOKK₂ <;> assumption)
