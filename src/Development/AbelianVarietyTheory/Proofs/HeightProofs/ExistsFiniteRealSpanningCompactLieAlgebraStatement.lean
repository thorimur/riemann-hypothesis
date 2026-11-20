import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFiniteRealSpanningCompactLieAlgebra
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_real_spanning_compactLieAlgebra : ∀ {n : ℕ} (ε : Fin n → Bool), ∃ (r : ℕ) (X : Fin r → Mx n), (∀ j, inK ε (X j)) ∧ ∀ Y, inK ε Y → ∃ c : Fin r → ℝ, Y = ∑ j, (c j : ℂ) • X j := by
  first | exact @GlobalTheory.KSpan.finite_real_span | exact GlobalTheory.KSpan.finite_real_span | (intros; apply GlobalTheory.KSpan.finite_real_span <;> assumption)
