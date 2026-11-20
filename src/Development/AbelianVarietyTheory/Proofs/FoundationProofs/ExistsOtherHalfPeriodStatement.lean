import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOtherHalfPeriod
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_half_period_sub_not_mem_of_isLat : ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ P : ℂ, 2 * P ∈ Λ → P ∉ Λ → ∃ P' : ℂ, 2 * P' ∈ Λ ∧ P' ∉ Λ ∧ P - P' ∉ Λ := by
  first | exact @GlobalTheory.HalfPeriod.exists_other_half_period | exact GlobalTheory.HalfPeriod.exists_other_half_period | (intros; apply GlobalTheory.HalfPeriod.exists_other_half_period <;> assumption)
