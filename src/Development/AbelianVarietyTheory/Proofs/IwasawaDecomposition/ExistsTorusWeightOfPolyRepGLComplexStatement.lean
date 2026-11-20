import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorusWeightOfPolyRepGLComplex
open Matrix GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torusWeight_of_polyRep_GL_complex : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∃ μ : Fin n → ℤ, IsWt Φ μ := by
  first | exact @GlobalTheory.AlgWtHW.exists_isWt_of_isPolyRep | exact GlobalTheory.AlgWtHW.exists_isWt_of_isPolyRep | (intros; apply GlobalTheory.AlgWtHW.exists_isWt_of_isPolyRep <;> assumption)
