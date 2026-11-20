import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

theorem UpperTheory.Reformulated.B.HeightShare.star_sqrt_neg :
    ∀ {D : Formalism.BasicNotions.D7} (x : D.host.E) (n : ℕ),
    (0 : ℕ) < n →
      x ^ (2 : ℕ) = -(↑n : D.host.E) →
        Star.star x =
          -x := by
  intro D x n hn hx
  haveI := D.host.isCMField_hostE
  have hc : D.host.φ₀ (star x) = starRingEnd ℂ (D.host.φ₀ x) :=
    NumberField.IsCMField.complexEmbedding_complexConj _ D.host.φ₀ x
  have h2 : star x ^ 2 = x ^ 2 := by rw [← star_pow, hx, star_neg, star_natCast]
  refine (sq_eq_sq_iff_eq_or_eq_neg.1 h2).resolve_left fun h => ?_
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 (h ▸ hc).symm
  have h3 : (r : ℂ) ^ 2 = -(n : ℂ) := by rw [← hr, ← map_pow, hx, map_neg, map_natCast]
  have h4 : r ^ 2 = -(n : ℝ) := by exact_mod_cast h3
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  nlinarith [sq_nonneg r]
