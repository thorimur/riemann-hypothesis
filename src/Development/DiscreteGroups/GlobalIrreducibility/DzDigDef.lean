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

namespace DiscreteGroups.sglob.DzType

def Dig : Prop :=
  ∀ (p n : ℕ), p.Prime → 2 ≤ n → 16 * n ^ 2 < p → ∀ k k' : ℕ,
    (∀ i j, i < n → j < n → k * p ^ i ≡ k * p ^ j [MOD p ^ n - 1] → i = j) →
    (∀ i j, i < n → j < n → k' * p ^ i ≡ k' * p ^ j [MOD p ^ n - 1] → i = j) →
    (∀ u b : ℕ, u.Coprime (p ^ n - 1) →
      (Nat.digits p ((u * k + b * ((p ^ n - 1) / (p - 1))) % (p ^ n - 1))).sum +
          (Nat.digits p (u * k' % (p ^ n - 1))).sum =
        (Nat.digits p ((u * k' + b * ((p ^ n - 1) / (p - 1))) % (p ^ n - 1))).sum +
          (Nat.digits p (u * k % (p ^ n - 1))).sum) →
    ∃ i : ℕ, k' ≡ k * p ^ i [MOD p ^ n - 1]

end DiscreteGroups.sglob.DzType
