import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePointWeightedPowerSumBound
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_point_weighted_power_sum_bound : ∀ (ι : Type) [Fintype ι] (s : ℝ), 1 < s → ∃ C : ℝ, ∀ (S : Type) (f : S → ι → ℝ) (K : ℝ) (A : ι → ℝ),
    (∀ c w, 0 ≤ f c w) → 0 ≤ K → (∀ w, 0 < A w) →
    (∀ T : ι → ℝ, (∀ w, 0 ≤ T w) → {c | ∀ w, f c w ≤ T w}.Finite ∧
      ({c | ∀ w, f c w ≤ T w}.ncard : ℝ) ≤ 1 + K * ∏ w, T w) →
    ∑' c : S, ENNReal.ofReal ((∏ w, (A w + f c w)) ^ (-s)) ≤
      ENNReal.ofReal (C * (1 + K * ∏ w, A w) * (∏ w, A w) ^ (-s)) := by
  first | exact @GlobalTheory.tsum_rpow_prod_add_le_of_box_count | exact GlobalTheory.tsum_rpow_prod_add_le_of_box_count | (intros; apply GlobalTheory.tsum_rpow_prod_add_le_of_box_count <;> assumption)
