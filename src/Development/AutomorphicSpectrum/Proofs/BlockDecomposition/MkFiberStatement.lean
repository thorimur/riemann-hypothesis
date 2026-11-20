import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MkFiber
open PositivityTheory.Rg.BcB.F.Tail.BS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_hecke_jacHk : JacHk := by
  first | exact @GlobalTheory.CompanionTheory.IwJac.jacHk | exact GlobalTheory.CompanionTheory.IwJac.jacHk | (intros; apply GlobalTheory.CompanionTheory.IwJac.jacHk <;> assumption)
