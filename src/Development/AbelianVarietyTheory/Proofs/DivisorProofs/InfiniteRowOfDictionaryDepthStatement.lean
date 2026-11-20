import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteRowOfDictionaryDepth
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinite_row_of_dictionary_depth : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → InfRowK := by
  first | exact @GlobalTheory.SumSize.OppConj.infRowK_main | exact GlobalTheory.SumSize.OppConj.infRowK_main | (intros; apply GlobalTheory.SumSize.OppConj.infRowK_main <;> assumption)
