import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorEigen
namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_eigen : PositivityTheory.Rg.BcB.F.Tail.PExp.TensEig := by
  first | exact @GlobalTheory.CompanionTheory.TensContr.tensEig | exact GlobalTheory.CompanionTheory.TensContr.tensEig | (intros; apply GlobalTheory.CompanionTheory.TensContr.tensEig <;> assumption)
