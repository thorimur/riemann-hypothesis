import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormIndependentTranslates
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspForm_independent_translates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], IndependentTranslates E := by
  first | exact @GlobalTheory.TranslatesDet.independentTranslates | exact GlobalTheory.TranslatesDet.independentTranslates | (intros; apply GlobalTheory.TranslatesDet.independentTranslates <;> assumption)
