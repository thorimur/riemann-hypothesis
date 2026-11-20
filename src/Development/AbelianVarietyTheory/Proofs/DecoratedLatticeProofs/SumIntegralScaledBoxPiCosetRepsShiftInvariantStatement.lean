import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumIntegralScaledBoxPiCosetRepsShiftInvariant
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_integralScaledBoxPi_coset_reps_shift_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (r R : kˣ) (S : Finset (n → k)), (∀ b ∈ S, b ∈ box n R) → (∀ a ∈ box n R, ∃! b, b ∈ S ∧ a - b ∈ box n r) → ∀ F : (n → k) → ℂ, (∀ t ∈ box n r, ∀ y, F (y + t) = F y) → ∀ a ∈ box n R, ∑ b ∈ S, F (a + b) = ∑ b ∈ S, F b := by
  first | exact @GlobalTheory.CosetSumShift.sum_shift | exact GlobalTheory.CosetSumShift.sum_shift | (intros; apply GlobalTheory.CosetSumShift.sum_shift <;> assumption)
