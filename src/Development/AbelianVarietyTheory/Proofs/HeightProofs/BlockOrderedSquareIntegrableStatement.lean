import Development.AbelianVarietyTheory.Proofs.HeightProofs.BlockOrderedSquareIntegrable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_ordered_square_integrable : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → IsSqIntOn ε σ := by
  first | exact @GlobalTheory.RealPar.SqInt.isSqIntOn_of_factors | exact GlobalTheory.RealPar.SqInt.isSqIntOn_of_factors | (intros; apply GlobalTheory.RealPar.SqInt.isSqIntOn_of_factors <;> assumption)
