import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PrincipalSum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.PrincipalSum : CompanionTheory.RgExh.Hk.PrinSum := by
  first | exact @GlobalTheory.CompanionTheory.PrinSumP.prinSum | exact GlobalTheory.CompanionTheory.PrinSumP.prinSum | (intros; apply GlobalTheory.CompanionTheory.PrinSumP.prinSum <;> assumption)
