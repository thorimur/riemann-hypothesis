import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HassePrincipleHermitian
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasse_principle_hermitian : Hasse := by
  first | exact @GlobalTheory.CompanionTheory.SW.BaseHasse.hasse | exact GlobalTheory.CompanionTheory.SW.BaseHasse.hasse | (intros; apply GlobalTheory.CompanionTheory.SW.BaseHasse.hasse <;> assumption)
