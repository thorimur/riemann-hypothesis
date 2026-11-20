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

namespace Bl.general_b_fact_upper_version

theorem goal1 :
  ∀ {R : Type} [inst : CommRing.{0} R] [IsDomain.{0} R] (ζ : R) (M : Nat) (P : Ideal.{0} R),
  Ne.{1} ζ 1 →
    Eq.{1} (HPow.hPow.{0, 0, 0} ζ M) 1 →
      Membership.mem.{0, 0} P (HSub.hSub.{0, 0, 0} ζ 1) → Membership.mem.{0, 0} P (Nat.cast.{0} M) := by
  intro R _ _ ζ M P h1 hM hP
  have hs : (∑ i ∈ Finset.range M, ζ ^ i) = 0 := by
    have h := geom_sum_mul ζ M
    rw [hM, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr h1)
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hP ⊢
  have h2 : Ideal.Quotient.mk P ζ = 1 := by
    rw [map_sub, map_one, sub_eq_zero] at hP
    exact hP
  have h3 := congrArg (Ideal.Quotient.mk P) hs
  simpa [map_sum, map_pow, h2] using h3

end Bl.general_b_fact_upper_version
