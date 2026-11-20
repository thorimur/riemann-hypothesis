import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransferOfSectionAndWallLaws
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transfer_of_section_and_wall_laws : PositivityTheory.RgEis.SecLaw → PositivityTheory.RgEis.WallLaw → PositivityTheory.RgEis.Transfer := by
  first | exact @GlobalTheory.CompanionTheory.RgTransfer.transfer | exact GlobalTheory.CompanionTheory.RgTransfer.transfer | (intros; apply GlobalTheory.CompanionTheory.RgTransfer.transfer <;> assumption)
