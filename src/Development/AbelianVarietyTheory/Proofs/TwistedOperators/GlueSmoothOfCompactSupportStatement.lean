import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlueSmoothOfCompactSupport
open GlobalTheory.Orb
open scoped Topology ContDiff Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_contDiff_comp_of_locally_smooth_compactSupport : ∀ (H : Type) [TopologicalSpace H] (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] (c : H → X) (f : H → ℂ), Continuous c → HasCompactSupport f → (∀ a, ∃ V : Set X, IsOpen V ∧ c a ∈ V ∧ ∃ Φ : X → ℂ, ContDiffOn ℝ ∞ Φ V ∧ ∀ g, c g ∈ V → f g = Φ (c g)) → ∃ Φ : X → ℂ, ContDiff ℝ ∞ Φ ∧ ∀ g, f g = Φ (c g) := by
  first | exact @GlobalTheory.glue_smooth_of_compactSupport | exact GlobalTheory.glue_smooth_of_compactSupport | (intros; apply GlobalTheory.glue_smooth_of_compactSupport <;> assumption)
