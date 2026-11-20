import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralBoxInvariantEqMeasureRealMulSumReps
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_box_invariant_eq_measureReal_mul_sum_reps : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (n : Type) [Fintype n] (r R : kˣ) (S : Finset (n → k)), (∀ b ∈ S, b ∈ box n R) → (∀ a ∈ box n R, ∃! b, b ∈ S ∧ a - b ∈ box n r) → ∀ F : (n → k) → ℂ, (∀ t ∈ box n r, ∀ y, F (y + t) = F y) → (∀ y ∉ box n R, F y = 0) → ∫ y, F y ∂(Measure.pi fun _ => ν) = ((Measure.pi fun _ : n => ν).real (box n r) : ℂ) * ∑ b ∈ S, F b := by
  first | exact @GlobalTheory.SplitWeil.FourierPi.integral_eq_measureReal_box_mul_sum | exact GlobalTheory.SplitWeil.FourierPi.integral_eq_measureReal_box_mul_sum | (intros; apply GlobalTheory.SplitWeil.FourierPi.integral_eq_measureReal_box_mul_sum <;> assumption)
