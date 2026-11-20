import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VerticalStatementHolds
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_mul_norm_rpow_neg_half' : Continuous fun z : ℂ => z * ((‖z‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  first | (exact @GlobalTheory.continuous_mul_norm_rpow_neg_half) | (exact GlobalTheory.continuous_mul_norm_rpow_neg_half) | (intros; apply GlobalTheory.continuous_mul_norm_rpow_neg_half  <;> assumption)
