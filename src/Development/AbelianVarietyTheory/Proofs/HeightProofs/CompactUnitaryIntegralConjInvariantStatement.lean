import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryIntegralConjInvariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compactUnitary_fourierKernel : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ), ∃ e, GlobalTheory.KFourier.IsKer ε i e := by
  first | exact @GlobalTheory.KFourier.exists_isKer | exact GlobalTheory.KFourier.exists_isKer | (intros; apply GlobalTheory.KFourier.exists_isKer <;> assumption)
