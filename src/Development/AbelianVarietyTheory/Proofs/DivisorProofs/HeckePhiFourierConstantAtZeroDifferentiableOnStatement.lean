import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierConstantAtZeroDifferentiableOn
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckePhiFourierConstantAtZero_differentiableOn : DifferentiableOn ℂ GlobalTheory.HeckeTwo.cConst GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane := by
  first | exact @GlobalTheory.HeckeTwo.cConst_differentiableOn | exact GlobalTheory.HeckeTwo.cConst_differentiableOn | (intros; apply GlobalTheory.HeckeTwo.cConst_differentiableOn <;> assumption)
