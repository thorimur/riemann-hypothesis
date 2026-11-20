import Development.AbelianVarietyTheory.Proofs.HeightProofs.HasSumCompactUnitaryFourierValueOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_compactUnitaryFourier_value_one : ∀ {n : ℕ} (ε : Fin n → Bool) (e : ℕ → KG ε → ℂ), (∀ i, GlobalTheory.KFourier.IsKer ε i (e i)) → ∀ g : KG ε → ℂ, Continuous g → ∀ b : ℕ → ℝ, Summable b → (∀ i (k' : KG ε), ‖∫ k, e i k * g (k' * k) ∂(muK ε)‖ ≤ b i) → HasSum (fun i => ∫ k, e i k * g k ∂(muK ε)) (g 1) := by
  first | exact @GlobalTheory.KFourier.hasSum_kFourier | exact GlobalTheory.KFourier.hasSum_kFourier | (intros; apply GlobalTheory.KFourier.hasSum_kFourier <;> assumption)
