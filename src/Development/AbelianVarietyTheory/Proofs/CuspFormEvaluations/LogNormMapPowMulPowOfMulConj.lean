import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init

open scoped BigOperators

namespace GlobalTheory

theorem norm_map_eq_sqrt_of_mul_conj {K : Type*} [Semiring K] (σ : K →+* ℂ) (x y : K) (g : ℕ)
    (hxy : x * y = g) (hy : σ y = starRingEnd ℂ (σ x)) : ‖σ x‖ = (g : ℝ) ^ (1 / 2 : ℝ) := by
  have h : σ x * starRingEnd ℂ (σ x) = (g : ℂ) := by
    rw [← hy, ← map_mul, hxy, map_natCast]
  have h2 : ((‖σ x‖ : ℝ) : ℂ) ^ 2 = (g : ℂ) := by
    rw [← Complex.mul_conj', h]
  have h3 : ‖σ x‖ ^ 2 = (g : ℝ) := by exact_mod_cast h2
  rw [← Real.sqrt_eq_rpow, ← h3, Real.sqrt_sq (norm_nonneg _)]

theorem norm_map_pow_mul_pow_of_mul_conj {K : Type*} [Semiring K] (σ : K →+* ℂ) (x y : K) (g : ℕ)
    (hxy : x * y = g) (hy : σ y = starRingEnd ℂ (σ x)) (a b : ℕ) :
    ‖σ (x ^ a * y ^ b)‖ = (g : ℝ) ^ (((a : ℝ) + b) / 2) := by
  have h1 := norm_map_eq_sqrt_of_mul_conj σ x y g hxy hy
  have hyn : ‖σ y‖ = ‖σ x‖ := by rw [hy]; simp
  rw [map_mul, map_pow, map_pow, norm_mul, norm_pow, norm_pow, hyn, ← pow_add, h1,
    ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg g)]
  congr 1
  push_cast
  ring

end GlobalTheory
