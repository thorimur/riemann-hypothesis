import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalAlgebraHolds
open PositivityTheory.Rg.BcB.F.Eig
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_algebra_holds : LocAlg := by
  first | exact @GlobalTheory.CompanionTheory.LocHecke.locAlg | exact GlobalTheory.CompanionTheory.LocHecke.locAlg | (intros; apply GlobalTheory.CompanionTheory.LocHecke.locAlg <;> assumption)
