import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LineFormulaOfFubiniAndParabolic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_formula_of_fubini_and_parabolic : CompanionTheory.RgExh.Dec.N.S.Fub2 → CompanionTheory.RgExh.Dec.N.S.LineFacts → CompanionTheory.RgExh.Dec.N.S.PSubEq → CompanionTheory.RgExh.Dec.L.LineFormula := by
  first | exact @GlobalTheory.CompanionTheory.RgLineFormula.lineFormula | exact GlobalTheory.CompanionTheory.RgLineFormula.lineFormula | (intros; apply GlobalTheory.CompanionTheory.RgLineFormula.lineFormula <;> assumption)
