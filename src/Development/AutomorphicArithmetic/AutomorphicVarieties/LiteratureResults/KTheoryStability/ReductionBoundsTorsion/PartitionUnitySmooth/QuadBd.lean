import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Topology.Sheaves.Init

open Matrix

namespace PositivityTheory.KB.SmoothPartitionUnityBasic.DerivationBounds

theorem quad_bd (N : ℕ) (V : Matrix (Fin N) (Fin N) ℂ) (M : ℝ) (hM : 0 ≤ M) (hV : ∀ a b, ‖V a b‖ ≤ M)
    (y : Fin N → ℂ) : |(star y ⬝ᵥ (V *ᵥ y)).re| ≤ N * M * (star y ⬝ᵥ y).re := by
  have e1 : star y ⬝ᵥ (V *ᵥ y) = ∑ a, ∑ b, star (y a) * V a b * y b := by
    simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have e2 : (star y ⬝ᵥ y).re = ∑ a, ‖y a‖ ^ 2 := by
    simp only [dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.mul_re]
  rw [e2]
  calc |(star y ⬝ᵥ (V *ᵥ y)).re| ≤ ‖star y ⬝ᵥ (V *ᵥ y)‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ a, ∑ b, ‖y a‖ * M * ‖y b‖ := by
        rw [e1]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        rw [norm_mul, norm_mul, norm_star]
        gcongr
        exact hV a b
    _ ≤ ∑ a, ∑ b, (M / 2 * ‖y a‖ ^ 2 + M / 2 * ‖y b‖ ^ 2) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        nlinarith [mul_nonneg hM (sq_nonneg (‖y a‖ - ‖y b‖))]
    _ = N * M * ∑ a, ‖y a‖ ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ← Finset.mul_sum]
        ring

end PositivityTheory.KB.SmoothPartitionUnityBasic.DerivationBounds
