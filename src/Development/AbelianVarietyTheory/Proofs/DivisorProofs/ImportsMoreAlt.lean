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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory.AbelianSumIdentityThird

theorem main : ∀ {S : Type} [inst : Ring S] (ε a b Gi K : S), (∀ (x : S), ε * x = x * ε) → ε * ε = ε → ε * a = a → ε * b = b → ((1 : S) - K) * a = ε → a * ((1 : S) - K) = ε → ((1 : S) - Gi * K) * b = ε → b * ((1 : S) - Gi * K) = ε → ((1 : S) - ε + b * ((1 : S) - K)) * ((1 : S) - ε + a * ((1 : S) - Gi * K)) = (1 : S) ∧ ((1 : S) - ε + a * ((1 : S) - Gi * K)) * ((1 : S) - ε + b * ((1 : S) - K)) = (1 : S) := by
  intro S _ ε a b Gi K hc hε ha hb h1 h2 h3 h4
  have haε : a * ε = a := by rw [← hc]; exact ha
  have hbε : b * ε = b := by rw [← hc]; exact hb
  have t1 : (1 - ε) * (1 - ε) = 1 - ε := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hε, sub_self, sub_zero]
  have t2a : (1 - ε) * a = 0 := by rw [sub_mul, one_mul, ha, sub_self]
  have t2b : (1 - ε) * b = 0 := by rw [sub_mul, one_mul, hb, sub_self]
  have t3 : ∀ x y : S, x * ε = x → x * y * (1 - ε) = 0 := by
    intro x y hx
    rw [mul_sub, mul_one, mul_assoc, ← hc y, ← mul_assoc, hx, sub_self]
  constructor
  · have e : b * (1 - K) * (a * (1 - Gi * K)) = ε := by
      rw [← mul_assoc, mul_assoc b, h1, hbε, h4]
    calc (1 - ε + b * (1 - K)) * (1 - ε + a * (1 - Gi * K))
        = (1 - ε) * (1 - ε) + (1 - ε) * a * (1 - Gi * K) + b * (1 - K) * (1 - ε)
          + b * (1 - K) * (a * (1 - Gi * K)) := by noncomm_ring
      _ = 1 := by rw [t1, t2a, t3 b _ hbε, e]; noncomm_ring
  · have e : a * (1 - Gi * K) * (b * (1 - K)) = ε := by
      rw [← mul_assoc, mul_assoc a, h3, haε, h2]
    calc (1 - ε + a * (1 - Gi * K)) * (1 - ε + b * (1 - K))
        = (1 - ε) * (1 - ε) + (1 - ε) * b * (1 - K) + a * (1 - Gi * K) * (1 - ε)
          + a * (1 - Gi * K) * (b * (1 - K)) := by noncomm_ring
      _ = 1 := by rw [t1, t2b, t3 a _ haε, e]; noncomm_ring

end GlobalTheory.AbelianSumIdentityThird
