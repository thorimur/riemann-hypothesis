import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BiInvariantReplaceSameDoubleCosetSums
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.biInvariant_replace_same_double_coset_sums : DosetSwap := by
  first | exact @GlobalTheory.InertZeta.dosetSwap | exact GlobalTheory.InertZeta.dosetSwap | (intros; apply GlobalTheory.InertZeta.dosetSwap <;> assumption)
