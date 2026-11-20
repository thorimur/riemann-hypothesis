import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralRetractionFiniteExtensionQl
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_retraction_finiteExtension_ql : ∀ (l : ℕ) [Fact l.Prime] (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1), ∃ r : ↥LL'.1 →ₗ[ℚ_[l]] ↥LL.1, (∀ a x, r (incl hL a * x) = a * r x) ∧ r 1 = 1 ∧ (∀ x ∈ OL LL', r x ∈ OL LL) := by
  first | exact @GlobalTheory.CoefRetraction.exists_integral_retraction | exact GlobalTheory.CoefRetraction.exists_integral_retraction | (intros; apply GlobalTheory.CoefRetraction.exists_integral_retraction <;> assumption)
