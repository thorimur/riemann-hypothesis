import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosineCountOfHyp
open GlobalTheory.SumCount GlobalTheory.SumSize
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosine_count_of_hypotheses : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.SumCount.CosK := by
  first | exact @GlobalTheory.CosCount.cosK | exact GlobalTheory.CosCount.cosK | (intros; apply GlobalTheory.CosCount.cosK <;> assumption)
