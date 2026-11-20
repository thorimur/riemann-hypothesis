import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace Bl.general_b_fact_left

theorem goal1 :
  ∀ {k : Type} [inst : Field.{0} k] [Fintype.{0} k] (t m e : k),
  Ne.{1} (HSub.hSub.{0, 0, 0} (HPow.hPow.{0, 0, 0} t 2) (HMul.hMul.{0, 0, 0} 4 m)) 0 →
    Exists.{1} fun (x : k) ↦
      Exists.{1} fun (y : k) ↦
        Eq.{1}
          (HAdd.hAdd.{0, 0, 0}
            (HAdd.hAdd.{0, 0, 0} (HPow.hPow.{0, 0, 0} x 2) (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} t x) y))
            (HMul.hMul.{0, 0, 0} m (HPow.hPow.{0, 0, 0} y 2)))
          e := by
  intro k _ _ t m e hd
  by_cases hc : ringChar k = 2
  · have h2 : (2 : k) = 0 := by
      have := ringChar.Nat.cast_ringChar (R := k)
      rwa [hc, Nat.cast_ofNat] at this
    have h4 : (4 : k) = 0 := by
      have : (4 : k) = 2 * 2 := by norm_num
      rw [this, h2, zero_mul]
    rw [h4, zero_mul, sub_zero] at hd
    have ht : t ≠ 0 := fun h => hd (by rw [h]; ring)
    by_cases hm : m = 0
    · refine ⟨1, (e - 1) / t, ?_⟩
      rw [hm]
      field_simp
      ring
    · obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two hc (e / m)
      refine ⟨0, r, ?_⟩
      have : r ^ 2 = e / m := by rw [hr]; ring
      rw [this]
      field_simp
      ring
  · have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hc
    have h4 : (4 : k) ≠ 0 := by
      have : (4 : k) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2 h2
    set D : k := m - t ^ 2 / 4 with hD
    have hD0 : D ≠ 0 := by
      intro h0
      apply hd
      have : t ^ 2 - 4 * m = -4 * D := by rw [hD]; field_simp; ring
      rw [this, h0, mul_zero]
    have hf : Polynomial.degree (Polynomial.X ^ 2 - Polynomial.C e : Polynomial k) = 2 := by
      rw [Polynomial.degree_sub_C] <;> rw [Polynomial.degree_X_pow] <;> norm_num
    have hg : Polynomial.degree (Polynomial.C D * Polynomial.X ^ 2 : Polynomial k) = 2 := by
      rw [Polynomial.degree_C_mul_X_pow 2 hD0]; rfl
    obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic hf hg
      (FiniteField.odd_card_of_char_ne_two hc)
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_mul] at hab
    refine ⟨a - t * b / 2, b, ?_⟩
    have key : a ^ 2 + D * b ^ 2 = e := by linear_combination hab
    rw [← key, hD]
    field_simp
    ring

end Bl.general_b_fact_left
