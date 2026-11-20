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

theorem UpperTheory.Reformulated.B.Qf4.pow_sub_one_mem :
    ∀ {S : Type} [inst : CommRing S] (J : Ideal S) (p : ℕ),
    Nat.Prime p → (↑p : S) ∈ J → ∀ (x : S), x - (1 : S) ∈ J → ∀ (j : ℕ), x ^ p ^ j - (1 : S) ∈ J ^ (j + (1 : ℕ)) := by
  intro S _ J p _ hp x hx j
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    have h1 : x ^ p ^ j - 1 ∈ J := Ideal.pow_le_self (Nat.succ_ne_zero j) ih
    have h2 : (∑ i ∈ Finset.range p, (x ^ p ^ j) ^ i) ∈ J := by
      have h3 : (∑ i ∈ Finset.range p, (x ^ p ^ j) ^ i)
          = (∑ i ∈ Finset.range p, ((x ^ p ^ j) ^ i - 1)) + (p : S) := by
        simp [Finset.sum_sub_distrib]
      rw [h3]
      refine J.add_mem (J.sum_mem fun i _ => ?_) hp
      exact J.mem_of_dvd (sub_one_dvd_pow_sub_one _ i) h1
    rw [pow_succ p j, pow_mul, ← mul_geom_sum, pow_succ J (j + 1)]
    exact Ideal.mul_mem_mul ih h2
