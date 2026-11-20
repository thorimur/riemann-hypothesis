import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersLevelOneEqSumZetaPow
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_eq_sum_zeta_pow_level_one : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (ζ : Om l), IsPrimitiveRoot ζ l → ∀ α : Om l, α ∈ Ks K 1 → ‖α‖ ≤ 1 → ∃ y : Fin l → Om l, (∀ a, y a ∈ K0 K ∧ ‖y a‖ ≤ 1) ∧ α = ∑ a : Fin l, ζ ^ (a : ℕ) * y a := by
  first | exact @GlobalTheory.Cyc.integers_level_one_eq_sum_zeta_pow | exact GlobalTheory.Cyc.integers_level_one_eq_sum_zeta_pow | (intros; apply GlobalTheory.Cyc.integers_level_one_eq_sum_zeta_pow <;> assumption)
