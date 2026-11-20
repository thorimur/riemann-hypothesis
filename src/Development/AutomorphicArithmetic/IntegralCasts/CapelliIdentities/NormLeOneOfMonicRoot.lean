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

theorem UpperTheory.Reformulated.B.NormLeOneOfMonicRoot.norm_le_one_of_monic_root.{u_1, u_2} :
    ∀ {R : Type u_1} {L : Type u_2} [inst : CommRing R] [inst_1 : NormedField L] [IsUltrametricDist L]
    (φ : R →+* L),
    (∀ (a : R), ‖(φ : R → L) a‖ ≤ (1 : ℝ)) →
      ∀ (x : L) (p : Polynomial R), p.Monic → Polynomial.eval₂ φ x p = (0 : L) → ‖x‖ ≤ (1 : ℝ) := by
  intro R L _ _ _ φ hφ x p hp hx
  by_contra hlt
  have h1 : 1 < ‖x‖ := not_le.mp hlt
  have h0 : 0 < ‖x‖ := lt_trans one_pos h1
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one,
    one_mul] at hx
  have hx' : x ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree, φ (p.coeff i) * x ^ i :=
    eq_neg_of_add_eq_zero_right hx
  have hb : ‖∑ i ∈ Finset.range p.natDegree, φ (p.coeff i) * x ^ i‖
      ≤ ‖x‖ ^ p.natDegree / ‖x‖ := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    have hi' : i + 1 ≤ p.natDegree := Finset.mem_range.mp hi
    rw [norm_mul, norm_pow, le_div_iff₀ h0]
    calc ‖φ (p.coeff i)‖ * ‖x‖ ^ i * ‖x‖ ≤ 1 * ‖x‖ ^ i * ‖x‖ := by
          gcongr
          exact hφ _
      _ = ‖x‖ ^ (i + 1) := by ring
      _ ≤ ‖x‖ ^ p.natDegree := pow_le_pow_right₀ h1.le hi'
  rw [← norm_neg, ← hx', norm_pow] at hb
  have hlt' : ‖x‖ ^ p.natDegree / ‖x‖ < ‖x‖ ^ p.natDegree :=
    div_lt_self (by positivity) h1
  exact absurd hb (not_le.mpr hlt')
