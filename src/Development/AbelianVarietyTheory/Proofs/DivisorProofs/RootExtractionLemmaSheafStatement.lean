import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootExtractionLemmaSheaf
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_extraction_lemma_sheaf : RootStatement := by
  first | exact @GlobalTheory.RootTrick.root_statement | exact GlobalTheory.RootTrick.root_statement | (intros; apply GlobalTheory.RootTrick.root_statement <;> assumption)
