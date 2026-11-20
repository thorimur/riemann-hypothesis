import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTopOfDictionaryDepth
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_top_of_dictionary_depth : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → FinTopK := by
  first | exact @GlobalTheory.SumSize.TopInt.finTopK | exact GlobalTheory.SumSize.TopInt.finTopK | (intros; apply GlobalTheory.SumSize.TopInt.finTopK <;> assumption)
