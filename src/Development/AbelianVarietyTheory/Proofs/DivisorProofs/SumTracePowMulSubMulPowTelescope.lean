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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory.ChernCalc

theorem sum_trace_pow_mul_sub_mul_pow (R : Type) [CommRing R] (r : Type) [Fintype r]
    [DecidableEq r] (P Q : Matrix r r R) (k : ℕ) :
    ∑ i ∈ Finset.range k, (P ^ i * (P - Q) * Q ^ (k - 1 - i)).trace
      = (P ^ k).trace - (Q ^ k).trace := by
  have h : ∀ i ∈ Finset.range k, (P ^ i * (P - Q) * Q ^ (k - 1 - i)).trace
      = (P ^ (i + 1) * Q ^ (k - (i + 1))).trace - (P ^ i * Q ^ (k - i)).trace := by
    intro i hi
    have hi' : i < k := Finset.mem_range.mp hi
    have e1 : k - 1 - i = k - (i + 1) := by omega
    have e2 : k - i = (k - (i + 1)) + 1 := by omega
    rw [e1, e2, ← Matrix.trace_sub, mul_sub, sub_mul, ← pow_succ, pow_succ' Q, mul_assoc]
  rw [Finset.sum_congr rfl h,
    Finset.sum_range_sub (fun i => (P ^ i * Q ^ (k - i)).trace)]
  simp

end GlobalTheory.ChernCalc
