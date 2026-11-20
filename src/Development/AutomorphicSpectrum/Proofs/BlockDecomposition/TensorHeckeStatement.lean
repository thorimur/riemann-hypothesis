import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorHecke
namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_hecke : PositivityTheory.Rg.BcB.F.Tail.PExp.TensHk := by
  first | exact @GlobalTheory.CompanionTheory.TensHkSum.tensHk | exact GlobalTheory.CompanionTheory.TensHkSum.tensHk | (intros; apply GlobalTheory.CompanionTheory.TensHkSum.tensHk <;> assumption)
