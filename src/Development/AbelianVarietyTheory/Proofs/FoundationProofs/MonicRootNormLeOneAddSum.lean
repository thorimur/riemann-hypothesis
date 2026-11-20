import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
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
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem monic_root_norm_le_one_add_sum :
    ∀ (n : ℕ) (s : Fin n → ℂ) (y : ℂ), y ^ n + ∑ j, s j * y ^ (j : ℕ) = 0 →
      ‖y‖ ≤ 1 + ∑ j, ‖s j‖ := by
  intro n s y h
  have hS : 0 ≤ ∑ j, ‖s j‖ := Finset.sum_nonneg (fun j _ => norm_nonneg _)
  by_cases hy : ‖y‖ ≤ 1
  · linarith
  push_neg at hy
  cases n with
  | zero => simp at h
  | succ m =>
    have hyn : y ^ (m + 1) = -∑ j, s j * y ^ (j : ℕ) := eq_neg_of_add_eq_zero_left h
    have h1 : ‖y‖ ^ (m + 1) ≤ ∑ j, ‖s j‖ * ‖y‖ ^ (j : ℕ) := by
      rw [← norm_pow, hyn, norm_neg]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [norm_mul, norm_pow]
    have h2 : ∑ j : Fin (m + 1), ‖s j‖ * ‖y‖ ^ (j : ℕ) ≤ (∑ j, ‖s j‖) * ‖y‖ ^ m := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact pow_le_pow_right₀ hy.le (Nat.lt_succ_iff.mp j.isLt)
    have h3 : ‖y‖ ^ (m + 1) = ‖y‖ * ‖y‖ ^ m := pow_succ' _ _
    have hpos : 0 < ‖y‖ ^ m := pow_pos (by linarith) m
    have h4 : ‖y‖ ≤ ∑ j, ‖s j‖ := by
      have h5 := h1.trans h2
      rw [h3] at h5
      exact le_of_mul_le_mul_right h5 hpos
    linarith

end GlobalTheory
