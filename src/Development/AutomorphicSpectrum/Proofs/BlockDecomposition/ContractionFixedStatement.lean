import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionFixed
namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contraction_fixed : PositivityTheory.Rg.BcB.F.Tail.PExp.ContrFix := by
  first | exact @GlobalTheory.CompanionTheory.RepTensor.contrFix | exact GlobalTheory.CompanionTheory.RepTensor.contrFix | (intros; apply GlobalTheory.CompanionTheory.RepTensor.contrFix <;> assumption)
