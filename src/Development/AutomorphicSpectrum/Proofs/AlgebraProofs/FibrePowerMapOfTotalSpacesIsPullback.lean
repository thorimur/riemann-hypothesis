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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.AbelFlag

theorem abel_summation_flag : ∀ (n : ℕ) (a : Fin (n + 1) → ℝ) (d : Fin (n + 2) → ℝ), d 0 = 0 →
    -(∑ i : Fin (n + 1), a i * (d i.succ - d i.castSucc)) =
      (∑ i : Fin n, (a i.castSucc - a i.succ) * (-d i.succ.castSucc))
        + a (Fin.last n) * (-d (Fin.last (n + 1))) := by
  intro n
  induction n with
  | zero =>
    intro a d h
    simp [h]
  | succ n ih =>
    intro a d h
    have key := ih (fun i => a i.castSucc) (fun i => d i.castSucc) (by simpa using h)
    rw [Fin.sum_univ_castSucc (n := n + 1), Fin.sum_univ_castSucc (n := n)
      (f := fun i : Fin (n + 1) => (a i.castSucc - a i.succ) * (-d i.succ.castSucc))]
    simp only [Fin.succ_castSucc, Fin.succ_last] at key ⊢
    linear_combination key

end GlobalTheory.CompanionTheory.AbelFlag
