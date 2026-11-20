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

namespace GlobalTheory.AlgebraicIntegerNormBound

theorem main : ∀ {A : Type} [inst : CommRing A] [IsDedekindDomain A] {Q : Ideal A} [Ideal.IsPrime Q], Q ≠ ⊥ → ∀ {π : A}, π ∈ Q → π ∉ Q ^ (2 : ℕ) → ∀ (m : ℕ), π ^ m ∉ Q ^ (m + (1 : ℕ)) := by
  intro A _ _ Q hQ hQ0 π h1 h2 m hm
  have hP : Prime Q := Ideal.prime_of_isPrime hQ0 hQ
  rw [← Ideal.dvd_span_singleton] at h1 h2 hm
  obtain ⟨J, hJ⟩ := h1
  have hJQ : ¬ Q ∣ J := by
    rintro ⟨K, hK⟩
    apply h2
    exact ⟨K, by rw [hJ, hK, pow_two, mul_assoc]⟩
  rw [← Ideal.span_singleton_pow, hJ, mul_pow, pow_succ] at hm
  have hQm : Q ^ m ≠ 0 := pow_ne_zero _ hQ0
  rw [mul_dvd_mul_iff_left hQm] at hm
  exact hJQ (hP.dvd_of_dvd_pow hm)

end GlobalTheory.AlgebraicIntegerNormBound
