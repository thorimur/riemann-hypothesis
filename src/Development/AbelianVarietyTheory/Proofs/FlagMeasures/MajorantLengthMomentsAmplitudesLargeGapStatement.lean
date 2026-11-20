import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantLengthMomentsAmplitudesLargeGap
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.majorantLength_moments_amplitudes_largeGap : GlobalTheory.GapIn.Hyp → ∀ Cg cb Cu cT CT C0 C1 Cq : ℝ, ∃ C : ℝ, ∀ Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), 1000 ≤ Cl → Big D large₂ Cl m₀ → MomIn D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C := by
  first | exact @GlobalTheory.AmpMomentsGap.amplitude_moments_gap | exact GlobalTheory.AmpMomentsGap.amplitude_moments_gap | (intros; apply GlobalTheory.AmpMomentsGap.amplitude_moments_gap <;> assumption)
