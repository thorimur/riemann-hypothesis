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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf

namespace GlobalTheory.ThreeDistinctRoots

open Polynomial

theorem three_distinct_roots :
    ∀ {K : Type} [inst : Field K] [IsAlgClosed K] (g₂ g₃ : K), (2 : K) ≠ (0 : K) →
      g₂ ^ (3 : ℕ) - (27 : K) * g₃ ^ (2 : ℕ) ≠ (0 : K) →
      ∃ (x : K) (y : K) (z : K), x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
        (4 : K) * x ^ (3 : ℕ) - g₂ * x - g₃ = (0 : K) ∧
        (4 : K) * y ^ (3 : ℕ) - g₂ * y - g₃ = (0 : K) ∧
        (4 : K) * z ^ (3 : ℕ) - g₂ * z - g₃ = (0 : K) := by
  intro K _ _ g₂ g₃ h2 hΔ
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2

  obtain ⟨x, hx⟩ : ∃ x : K, (4 : K) * x ^ 3 - g₂ * x - g₃ = 0 := by
    have hdeg : (C (4 : K) * X ^ 3 - C g₂ * X - C g₃).degree ≠ 0 := by
      have : (C (4 : K) * X ^ 3 - C g₂ * X - C g₃).degree = 3 := by
        compute_degree!
      rw [this]; decide
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hdeg
    refine ⟨x, ?_⟩
    simpa using hx

  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (g₂ - 3 * x ^ 2)
  obtain ⟨y, hy⟩ : ∃ y : K, 2 * y = s - x := ⟨(s - x) / 2, by field_simp⟩
  have hq : 4 * y ^ 2 + 4 * x * y + 4 * x ^ 2 - g₂ = 0 := by
    linear_combination (2 * y + x + s) * hy - hs
  have hg₂ : g₂ = 4 * (x ^ 2 + x * y + y ^ 2) := by linear_combination -hq
  have hg₃ : g₃ = -4 * x * y * (x + y) := by
    linear_combination -hx + x * hq
  refine ⟨x, y, -x - y, ?_⟩
  have key : g₂ ^ 3 - 27 * g₃ ^ 2 = 16 * ((x - y) * (y - (-x - y)) * ((-x - y) - x)) ^ 2 := by
    rw [hg₂, hg₃]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; apply hΔ; rw [key, sub_eq_zero.mpr h]; ring
  · intro h; apply hΔ
    rw [key, show (-x - y) - x = -(x - (-x - y)) by ring, sub_eq_zero.mpr h]; ring
  · intro h; apply hΔ
    rw [key, sub_eq_zero.mpr h]; ring
  · exact hx
  · rw [hg₂, hg₃]; ring
  · rw [hg₂, hg₃]; ring

end GlobalTheory.ThreeDistinctRoots
