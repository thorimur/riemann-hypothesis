import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSumRootsOfUnity
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_sum_padicInt_mul_rootsOfUnity : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (c : Om l), c ∈ K0 K → ‖c‖ ≤ 1 → ∃ (n : ℕ) (z : Fin n → ℤ_[l]) (ω : Fin n → Om l), (∀ i, ω i ∈ K0 K ∧ ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ ω i ^ m = 1) ∧ c = ∑ i, algebraMap ℚ_[l] (Om l) (z i : ℚ_[l]) * ω i := by
  first | exact @GlobalTheory.UnramSpan.exists_sum_rootsOfUnity | exact GlobalTheory.UnramSpan.exists_sum_rootsOfUnity | (intros; apply GlobalTheory.UnramSpan.exists_sum_rootsOfUnity <;> assumption)
