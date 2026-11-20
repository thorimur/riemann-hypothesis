import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepSumSurjectiveInitialSegment
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.step_sum_surjective_initial_segment : ∀ {r : ℕ} {S : Finset (Fin r)}, (∀ k ∈ S, ∀ i, i ≤ k → i ∈ S) → ∀ (v : Fin r → ℝ), (∀ i ∉ S, v i = 0) → ∃ u, stepSum S u = v := by
  first | exact @GlobalTheory.stepSum_surj_of_initial | exact GlobalTheory.stepSum_surj_of_initial | (intros; apply GlobalTheory.stepSum_surj_of_initial <;> assumption)
