import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDegreesSmallAgainstTypePrimes
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelDegrees_small_against_typePrimes : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D), ParameterChoice' D L → Formalism.MainNotions.SizesAt L → L.sc.eps = eps → x0 ≤ L.sc.x → ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.SizeAt D i := by
  first | exact @GlobalTheory.AtG.KernelSizes.sizeAt_of_params | exact GlobalTheory.AtG.KernelSizes.sizeAt_of_params | (intros; apply GlobalTheory.AtG.KernelSizes.sizeAt_of_params <;> assumption)
