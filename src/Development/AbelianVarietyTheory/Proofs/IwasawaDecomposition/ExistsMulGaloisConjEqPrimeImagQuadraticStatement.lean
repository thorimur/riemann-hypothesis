import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMulGaloisConjEqPrimeImagQuadratic
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mul_galois_conj_eq_prime_imagQuadratic : ∀ (K : Type) [Field K] [NumberField K], IsEmpty (K →+* ℝ) → Module.finrank ℚ K = 2 →
    ∀ (j : K →+* Qb) (π : 𝓞 K) (p : ℕ), Ideal.absNorm (Ideal.span {π}) = p →
      ∃ σ : Qb →ₐ[ℚ] Qb, j (π : K) * σ (j (π : K)) = (p : Qb) := by
  first | exact @GlobalTheory.RayFieldNorm.exists_mul_conj_eq_norm | exact GlobalTheory.RayFieldNorm.exists_mul_conj_eq_norm | (intros; apply GlobalTheory.RayFieldNorm.exists_mul_conj_eq_norm <;> assumption)
