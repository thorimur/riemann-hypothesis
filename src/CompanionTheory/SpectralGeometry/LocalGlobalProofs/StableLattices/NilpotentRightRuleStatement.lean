import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentRightRule
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.NilpotentRightRule : CompanionTheory.RgExh.Dec.N.RightRule := by
  first | exact @GlobalTheory.CompanionTheory.RightRule.rightRule | exact GlobalTheory.CompanionTheory.RightRule.rightRule | (intros; apply GlobalTheory.CompanionTheory.RightRule.rightRule <;> assumption)
