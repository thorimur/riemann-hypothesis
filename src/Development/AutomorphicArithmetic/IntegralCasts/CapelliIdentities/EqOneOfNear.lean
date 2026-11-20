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
import Mathlib.NumberTheory.Padics.Complex
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
import Mathlib.Topology.Sheaves.Init

namespace UpperTheory.Reformulated.B.S7

theorem eq_one_of_near {l : ℕ} [Fact l.Prime] {u : PadicAlgCl l} {m : ℕ} (hm : ¬ l ∣ m) (hu : u ^ m = 1)
    (h : ‖u - 1‖ < 1) : u = 1 := by
  by_contra hne
  have hu1 : ‖u‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (u - 1) 1
    rw [sub_add_cancel, norm_one] at this
    exact this.trans (max_le h.le le_rfl)
  have hpow : ∀ i : ℕ, ‖u ^ i - 1‖ < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : u ^ (i + 1) - 1 = (u ^ i - 1) * u + (u - 1) := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ h)
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hu1).trans_lt ih
  have hsum : ∀ n : ℕ, ‖(∑ i ∈ Finset.range n, u ^ i) - (n : PadicAlgCl l)‖ < 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : (∑ i ∈ Finset.range (n + 1), u ^ i) - ((n + 1 : ℕ) : PadicAlgCl l)
          = ((∑ i ∈ Finset.range n, u ^ i) - (n : PadicAlgCl l)) + (u ^ n - 1) := by
        rw [Finset.sum_range_succ]; push_cast; ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih (hpow n))
  have h0 : (∑ i ∈ Finset.range m, u ^ i) = 0 := by
    have := geom_sum_mul u m
    rw [hu, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
  have hlt := hsum m
  rw [h0, zero_sub, norm_neg] at hlt
  have e : (m : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (m : ℚ_[l]) := by simp
  rw [e, norm_algebraMap'] at hlt
  exact hm (Padic.norm_natCast_lt_one_iff.mp hlt)

end UpperTheory.Reformulated.B.S7
