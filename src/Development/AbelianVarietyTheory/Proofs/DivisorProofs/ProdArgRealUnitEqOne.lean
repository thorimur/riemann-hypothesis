import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Int.Star
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
open NumberField

namespace GlobalTheory

theorem prod_arg_real_unit_eq_one (E : Type) [Field E] [NumberField E] [IsCMField E] (q : ℕ)
    (hq : q.Prime) (hq2 : 2 < q)
    (u : (𝓞 E)ˣ) (hu : (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)})
    (hreal : ∀ φ : E →+* ℂ, starRingEnd ℂ (φ ((u : 𝓞 E) : E)) = φ ((u : 𝓞 E) : E)) :
    ∏ w : InfinitePlace E, (w.embedding ((u : 𝓞 E) : E) /
      ((‖w.embedding ((u : 𝓞 E) : E)‖ : ℝ) : ℂ)) = 1 := by
  set x : E := ((u : 𝓞 E) : E) with hx
  have hnorm : ∏ w : InfinitePlace E, ‖w.embedding x‖ = 1 := by
    have h1 := InfinitePlace.prod_eq_abs_norm x
    have hN : |Algebra.norm ℚ x| = 1 := Units.norm E u
    rw [hN] at h1
    have h2 : ∏ w : InfinitePlace E, w x ^ w.mult =
        (∏ w : InfinitePlace E, ‖w.embedding x‖) ^ 2 := by
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [IsTotallyComplex.mult_eq, InfinitePlace.norm_embedding_eq]
    rw [h2] at h1
    have h0 : 0 ≤ ∏ w : InfinitePlace E, ‖w.embedding x‖ :=
      Finset.prod_nonneg fun _ _ => norm_nonneg _
    exact (pow_eq_one_iff_of_nonneg h0 two_ne_zero).mp (by exact_mod_cast h1)
  rw [Finset.prod_div_distrib, ← Complex.ofReal_prod, hnorm, Complex.ofReal_one, div_one]
  set P : ℂ := ∏ w : InfinitePlace E, w.embedding x with hP
  have hPreal : starRingEnd ℂ P = P := by
    rw [hP, map_prod]
    exact Finset.prod_congr rfl fun w _ => hreal w.embedding
  have hPnorm : ‖P‖ = 1 := by rw [hP, norm_prod, hnorm]
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hu
  have hxy : x = 1 + ((y : 𝓞 E) : E) * (q : E) := by
    have : (u : 𝓞 E) = 1 + y * (q : 𝓞 E) := by rw [hy]; ring
    rw [hx, this]; push_cast; ring
  have hcong : ∃ s ∈ integralClosure ℤ ℂ, P = 1 + s * (q : ℂ) := by
    rw [hP]
    refine Finset.prod_induction _ (fun z => ∃ s ∈ integralClosure ℤ ℂ, z = 1 + s * (q : ℂ))
      ?_ ⟨0, zero_mem _, by ring⟩ ?_
    · rintro a b ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
      refine ⟨s + t + s * t * q, ?_, by ring⟩
      exact add_mem (add_mem hs ht) (mul_mem (mul_mem hs ht) (Subalgebra.natCast_mem _ q))
    · intro w _
      refine ⟨w.embedding ((y : 𝓞 E) : E), ?_, ?_⟩
      · rw [mem_integralClosure_iff]
        exact (RingOfIntegers.isIntegral_coe y).map w.embedding.toIntAlgHom
      · rw [hxy]; simp
  obtain ⟨s, hs, hPs⟩ := hcong
  have hre : P = (P.re : ℂ) := ((Complex.conj_eq_iff_re).mp hPreal).symm
  have habs : |P.re| = 1 := by
    rw [← hPnorm, hre, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
  rcases (abs_eq zero_le_one).mp habs with h | h
  · rw [hre, h, Complex.ofReal_one]
  · exfalso
    have hPm : P = -1 := by rw [hre, h]; simp
    have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne_zero
    have hs' : s = algebraMap ℚ ℂ (-2 / q) := by
      rw [hPm] at hPs
      rw [map_div₀, map_neg, map_ofNat, map_natCast]
      field_simp
      linear_combination -hPs
    rw [mem_integralClosure_iff, hs'] at hs
    have hint : IsIntegral ℤ ((-2 / q : ℚ)) :=
      (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).mp hs
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
    have h2 : (n : ℚ) * q = -2 := by
      rw [show (algebraMap ℤ ℚ n) = (n : ℚ) from rfl] at hn
      rw [hn]; field_simp
    have h3 : n * (q : ℤ) = -2 := by exact_mod_cast h2
    have h4 : (q : ℤ) ∣ 2 := ⟨-n, by linarith⟩
    have h5 : q ∣ 2 := by exact_mod_cast h4
    have := Nat.le_of_dvd two_pos h5
    omega

end GlobalTheory
