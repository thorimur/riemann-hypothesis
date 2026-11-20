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
import Mathlib.Tactic.Monotonicity.Lemmas
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

namespace Bl.general_b_fact_third

theorem goal1 :
  ∀ {K : Type u_1} [inst : NormedField.{u_1} K] [IsUltrametricDist.{u_1} K] (P : Polynomial.{u_1} K),
  Polynomial.Monic.{u_1} P →
    (∀ (i : Nat), LE.le.{0} (Norm.norm.{u_1} (Polynomial.coeff.{u_1} P i)) 1) →
      ∀ (x : K), Eq.{u_1 + 1} (Polynomial.eval.{u_1} x P) 0 → LE.le.{0} (Norm.norm.{u_1} x) 1 := by
  intro K _ _ P hP hc x hx
  by_contra h
  rw [not_le] at h
  have hx0 : (0:ℝ) < ‖x‖ := lt_trans one_pos h
  rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, hP.coeff_natDegree, one_mul] at hx
  have hS : ‖∑ i ∈ Finset.range P.natDegree, P.coeff i * x ^ i‖ ≤ ‖x‖ ^ P.natDegree / ‖x‖ := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [Finset.mem_range] at hi
    rw [norm_mul, norm_pow, le_div_iff₀ hx0]
    calc ‖P.coeff i‖ * ‖x‖ ^ i * ‖x‖ ≤ 1 * ‖x‖ ^ i * ‖x‖ := by
          gcongr
          exact hc i
      _ = ‖x‖ ^ (i + 1) := by rw [one_mul, pow_succ]
      _ ≤ ‖x‖ ^ P.natDegree := pow_le_pow_right₀ h.le (Nat.succ_le_of_lt hi)
  have heq : ∑ i ∈ Finset.range P.natDegree, P.coeff i * x ^ i = -(x ^ P.natDegree) :=
    eq_neg_of_add_eq_zero_left hx
  rw [heq, norm_neg, norm_pow] at hS
  have hpos : 0 < ‖x‖ ^ P.natDegree := pow_pos hx0 _
  have hlt : ‖x‖ ^ P.natDegree / ‖x‖ < ‖x‖ ^ P.natDegree := div_lt_self hpos h
  linarith

end Bl.general_b_fact_third
