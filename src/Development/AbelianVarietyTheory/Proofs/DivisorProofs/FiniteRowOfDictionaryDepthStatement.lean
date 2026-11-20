import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRowOfDictionaryDepth
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_row_of_dictionary_depth : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → FinRowK := by
  first | exact @GlobalTheory.SumSize.finRowK | exact GlobalTheory.SumSize.finRowK | (intros; apply GlobalTheory.SumSize.finRowK <;> assumption)
