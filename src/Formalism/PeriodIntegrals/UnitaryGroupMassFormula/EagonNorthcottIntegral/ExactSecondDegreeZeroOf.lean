import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.YHom

noncomputable section

namespace PI.EagonNorthcottZ

open MvPolynomial

private theorem sgn_one {D : ℕ} (i : Fin D) (J : Finset (Fin D)) (h : ∀ l ∈ J, ¬ l < i) : sgn i J = 1 := by
  unfold sgn
  rw [Finset.filter_eq_empty_iff.mpr h]; simp

end PI.EagonNorthcottZ
