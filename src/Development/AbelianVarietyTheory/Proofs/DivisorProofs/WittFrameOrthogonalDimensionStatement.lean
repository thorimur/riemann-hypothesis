import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameOrthogonalDimension
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes GlobalTheory.EisRestrict
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_frame_orthogonal_dimension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E),
    IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    dim σ J X Y + 2 = n := by
  first | exact @GlobalTheory.EisRestrict.dim_add_two | exact GlobalTheory.EisRestrict.dim_add_two | (intros; apply GlobalTheory.EisRestrict.dim_add_two <;> assumption)
