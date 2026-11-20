import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GammaFunctionBoundedSupport
open MeasureTheory Finset GlobalTheory.Chamber
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gamma_function_bounded_support : ∀ (k : ℕ) (P R : Finset (SV k)) (Y : A0 k), IsPar P → R ⊆ P → ∃ C : ℝ, ∀ H ∈ aMQ (aP P) R, gamP P R Y H ≠ 0 → ‖H‖ ≤ C := by
  first | exact @GlobalTheory.Chamber.gamP_bounded_support | exact GlobalTheory.Chamber.gamP_bounded_support | (intros; apply GlobalTheory.Chamber.gamP_bounded_support <;> assumption)
