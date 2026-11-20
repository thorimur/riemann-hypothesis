import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactUnitHolds
open PositivityTheory.Rg.BcB.F.Eig
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_unit_holds : CompUnit := by
  first | exact @GlobalTheory.CompanionTheory.CompUnitary.compUnit | exact GlobalTheory.CompanionTheory.CompUnitary.compUnit | (intros; apply GlobalTheory.CompanionTheory.CompUnitary.compUnit <;> assumption)
