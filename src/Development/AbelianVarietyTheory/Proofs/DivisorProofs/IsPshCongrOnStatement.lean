import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPshCongrOn

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPsh_congr_divisor : ∀ (D : ℕ) (U : Set (Fin D → ℂ)) (φ ψ : (Fin D → ℂ) → ℝ), ReciprocityTheory.AnForm.A.IsPsh U φ → (∀ z ∈ U, φ z = ψ z) → ReciprocityTheory.AnForm.A.IsPsh U ψ := by
  first | exact @GlobalTheory.isPsh_congr_on | exact GlobalTheory.isPsh_congr_on | (intros; apply GlobalTheory.isPsh_congr_on <;> assumption)
