import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionLawHolds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_law_holds : PositivityTheory.RgEis.SecLaw := by
  first | exact @GlobalTheory.CompanionTheory.RgEisSec.secLaw | exact GlobalTheory.CompanionTheory.RgEisSec.secLaw | (intros; apply GlobalTheory.CompanionTheory.RgEisSec.secLaw <;> assumption)
