import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteTopOfDictionaryDepth
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinite_top_of_dictionary_depth : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → InfTopK := by
  first | exact @GlobalTheory.KerConjMean.infTopK | exact GlobalTheory.KerConjMean.infTopK | (intros; apply GlobalTheory.KerConjMean.infTopK <;> assumption)
