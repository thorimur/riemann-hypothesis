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

namespace GlobalTheory.NatCastNotMemPrimeIdeal

theorem natCast_notMem_of_prime_ne {L : Type} [Field L] [NumberField L]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : q ≠ p)
    (hqw : (q : NumberField.RingOfIntegers L) ∈ w.asIdeal) :
    (p : NumberField.RingOfIntegers L) ∉ w.asIdeal := by
  intro hpw
  have hc : IsCoprime (q : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hq hp).mpr hne)
  obtain ⟨a, b, hab⟩ := hc
  have h1 : (a : NumberField.RingOfIntegers L) * (q : NumberField.RingOfIntegers L)
      + (b : NumberField.RingOfIntegers L) * (p : NumberField.RingOfIntegers L) = 1 := by
    have := congrArg (Int.cast : ℤ → NumberField.RingOfIntegers L) hab
    push_cast at this
    exact this
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← h1]
  exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hqw) (w.asIdeal.mul_mem_left _ hpw)

end GlobalTheory.NatCastNotMemPrimeIdeal
