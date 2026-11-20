import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
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

open NumberField

namespace GlobalTheory.CMModel

theorem isPrime_span_of_sq_eq_neg_prime :
    ∀ (p : ℕ) (K : Type) [Field K] [NumberField K] (y : 𝓞 K), p.Prime → Module.finrank ℚ K = 2 →
      y ^ 2 = -(p : 𝓞 K) → (Ideal.span {y}).IsPrime := by
  intro p K _ _ y hp hK hy
  have hr : Module.finrank ℤ (𝓞 K) = 2 := by rw [RingOfIntegers.rank, hK]
  have h1 : Ideal.absNorm (Ideal.span {y}) ^ 2 = p ^ 2 := by
    rw [← map_pow, Ideal.span_singleton_pow, hy, Ideal.span_singleton_neg,
      Ideal.absNorm_span_singleton]
    have : (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, hr]
    simp [Int.natAbs_pow]
  have h2 : Ideal.absNorm (Ideal.span {y}) = p :=
    Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) h1
  apply Ideal.isPrime_of_irreducible_absNorm
  rw [h2]
  exact (Nat.irreducible_iff_nat_prime p).2 hp

end GlobalTheory.CMModel
