import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryCoordFunMulEqSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactUnitary_fourierKernel_conj_invariant : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (e : KG ε → ℂ), GlobalTheory.KFourier.IsKer ε i e → ∀ a k : KG ε, e (a * k * a⁻¹) = e k := by
  first | exact @GlobalTheory.KFourier.isKer_class | exact GlobalTheory.KFourier.isKer_class | (intros; apply GlobalTheory.KFourier.isKer_class <;> assumption)
