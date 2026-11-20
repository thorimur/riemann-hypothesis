import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryRightDerivRealLinearDirection
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactUnitaryRightDeriv_real_linear_direction : ∀ {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (φ : KG ε → ℂ), φ ∈ polyV ε d → ∀ {r : ℕ} (X : Fin r → Mx n) (c : Fin r → ℝ), (∀ j, inK ε (X j)) → rder ε [∑ j, (c j : ℂ) • X j] φ = ∑ j, (c j : ℂ) • rder ε [X j] φ := by
  first | exact @GlobalTheory.KFourier.rder_real_linear | exact GlobalTheory.KFourier.rder_real_linear | (intros; apply GlobalTheory.KFourier.rder_real_linear <;> assumption)
