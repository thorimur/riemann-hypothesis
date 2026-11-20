import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPowMovesPadicRootOfUnity
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_pow_moves_padic_rootOfUnity : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}, FiniteDimensional ℚ_[p] K →
    ∀ k : ℕ, 0 < k → ∃ (σ : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 ∧ (σ ^ k) ζ ≠ ζ := by
  first | exact @GlobalTheory.ShapeNeg.exists_pow_ne_rootOfUnity | exact GlobalTheory.ShapeNeg.exists_pow_ne_rootOfUnity | (intros; apply GlobalTheory.ShapeNeg.exists_pow_ne_rootOfUnity <;> assumption)
