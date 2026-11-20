import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqZeroOfOrthogonalCompactUnitaryPolyFun
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.KFourier

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_orthogonal_compactUnitaryPolyFun : ∀ {n : ℕ} (ε : Fin n → Bool) (h : KG ε → ℂ), Continuous h → (∀ d, ∀ q ∈ GlobalTheory.KFourier.polyV ε d, ∫ k, star (q k) * h k ∂(muK ε) = 0) → h = 0 := by
  first | exact @GlobalTheory.KFourier.eq_zero_of_orth_poly | exact GlobalTheory.KFourier.eq_zero_of_orth_poly | (intros; apply GlobalTheory.KFourier.eq_zero_of_orth_poly <;> assumption)
