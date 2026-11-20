import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralInversePowerSeriesOfUnitConstantCo
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_inverse_powerSeries_of_unit_constantCoeff : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (f : K⟦X⟧), (∀ n, ‖coeff n f‖ ≤ 1) → ‖constantCoeff f‖ = 1 → ∃ g : K⟦X⟧, (∀ n, ‖coeff n g‖ ≤ 1) ∧ f * g = 1 := by
  first | exact @GlobalTheory.powerSeries_inv_coeff_norm_le_one | exact GlobalTheory.powerSeries_inv_coeff_norm_le_one | (intros; apply GlobalTheory.powerSeries_inv_coeff_norm_le_one <;> assumption)
