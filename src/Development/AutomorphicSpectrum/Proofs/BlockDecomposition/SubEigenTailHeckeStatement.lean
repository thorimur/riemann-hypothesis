import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubEigenTailHecke
namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sub_eigen_tail_hecke : PositivityTheory.Rg.BcB.F.Tail.PExp.SubEig := by
  first | exact @GlobalTheory.CompanionTheory.SubEigIrr.subEig | exact GlobalTheory.CompanionTheory.SubEigIrr.subEig | (intros; apply GlobalTheory.CompanionTheory.SubEigIrr.subEig <;> assumption)
