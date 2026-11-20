import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFontaineThetaFrobeniusInverseShift
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fontaineTheta_frobeniusInverse_shift : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (n : ℕ), ∃ θ : Ainf l →ₐ[ℤ_[l]] OC l, IsThetaShift AI n θ := by
  first | exact @GlobalTheory.Cyc.Decomp.exists_isThetaShift | exact GlobalTheory.Cyc.Decomp.exists_isThetaShift | (intros; apply GlobalTheory.Cyc.Decomp.exists_isThetaShift <;> assumption)
