import Development.AbelianVarietyTheory.Proofs.HeightProofs.PairingConvolutionSwap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.KFourier

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_star_mul_convolution_eq_integral_swap : ∀ {n : ℕ} (ε : Fin n → Bool) (e q g : KG ε → ℂ), Continuous e → Continuous q → Continuous g → ∫ k', star (q k') * ∫ k, e k * g (k' * k) ∂(muK ε) ∂(muK ε) = ∫ y, g y * ∫ x, e x * star (q (y * x⁻¹)) ∂(muK ε) ∂(muK ε) := by
  first | exact @GlobalTheory.KFourier.pairing_convolution_swap | exact GlobalTheory.KFourier.pairing_convolution_swap | (intros; apply GlobalTheory.KFourier.pairing_convolution_swap <;> assumption)
