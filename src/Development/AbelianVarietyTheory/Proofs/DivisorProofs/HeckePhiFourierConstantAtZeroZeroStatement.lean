import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierConstantAtZeroZero
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckePhiFourierConstantAtZero_zero : GlobalTheory.HeckeTwo.cConst 0 = 0 := by
  first | exact @GlobalTheory.HeckeTwo.cConst_zero | exact GlobalTheory.HeckeTwo.cConst_zero | (intros; apply GlobalTheory.HeckeTwo.cConst_zero <;> assumption)
