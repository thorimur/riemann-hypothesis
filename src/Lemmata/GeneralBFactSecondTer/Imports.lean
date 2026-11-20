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
import Std.Tactic.BVDecide.Normalize.Prop

namespace Bl.general_b_fact_second_ter

theorem goal1 :
  ∀ {n : Nat} (Q : Fin n → Prop) [inst : DecidablePred.{1} Q],
  (∀ (q q' : Fin n), LE.le.{0} q' q → Q q → Q q') →
    ∀ (p : Fin n), Iff (Q p) (LT.lt.{0} p.val (Finset.card.{0} (Finset.filter.{0} Q Finset.univ.{0}))) := by
  intro n Q _ hQ p
  constructor
  · intro hp
    have h : Finset.Iic p ⊆ Finset.filter Q Finset.univ := by
      intro q hq
      rw [Finset.mem_Iic] at hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hQ p q hq hp
    have hc := Finset.card_le_card h
    rw [Fin.card_Iic] at hc
    omega
  · intro hlt
    by_contra hp
    have h : Finset.filter Q Finset.univ ⊆ Finset.Iio p := by
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      rw [Finset.mem_Iio]
      by_contra hqp
      exact hp (hQ q p (not_lt.mp hqp) hq)
    have hc := Finset.card_le_card h
    rw [Fin.card_Iio] at hc
    omega

end Bl.general_b_fact_second_ter
