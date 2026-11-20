import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableHeckeTermDecayIntegrand
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermDecay
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_heckeTermDecayIntegrand : ∀ σ ∈ halfPlane, ∀ (a : ℤ) (b m : ℕ), 2 ≤ a + 2 * b → ∀ y : ℝ, y ≠ 0 →
    MeasureTheory.Integrable (qZ σ a b m y) := by
  first | exact @GlobalTheory.HeckeTwo.TermDecay.integrable_qZ | exact GlobalTheory.HeckeTwo.TermDecay.integrable_qZ | (intros; apply GlobalTheory.HeckeTwo.TermDecay.integrable_qZ <;> assumption)
