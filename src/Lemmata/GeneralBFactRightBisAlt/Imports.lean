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

universe u_1

namespace Bl.general_b_fact_right_bis_other

theorem goal1 :
  ∀ {K : Type u_1} [inst : CommRing.{u_1} K] {n : Nat} {l l' : Matrix.{0, 0, u_1} (Fin n) (Fin n) K},
  (∀ (a b : Fin n), LT.lt.{0} a b → Eq.{u_1 + 1} (l a b) 0) →
    (∀ (a b : Fin n), LT.lt.{0} a b → Eq.{u_1 + 1} (l' a b) 0) →
      ∀ (a : Fin n), Eq.{u_1 + 1} (HMul.hMul.{u_1, u_1, u_1} l l' a a) (HMul.hMul.{u_1, u_1, u_1} (l a a) (l' a a)) := by
  intro K _ n l l' hl hl' a
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single a ?_ ?_
  · intro c _ hca
    rcases lt_or_gt_of_ne hca with h | h
    · rw [hl' c a h, mul_zero]
    · rw [hl a c h, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

end Bl.general_b_fact_right_bis_other
