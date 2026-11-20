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
import Mathlib.RingTheory.Radical.NatInt
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

noncomputable section

namespace Formalism.CountingSumsFrames

open Real

namespace RoomIProof

theorem core (C Cm N1 k Q c La b' Ib X Nr Y Yb : ℝ)
    (hCm : 0 ≤ Cm) (hC : 192 + 32 * Cm ≤ C) (hN1 : 1 ≤ N1) (hk : 1 ≤ k) (hQ : 1 ≤ Q)
    (hLa : N1 ^ 2 ≤ La) (hYb : C ≤ Yb) (hb : 0 < b') (hc0 : 0 ≤ c) (hc : c ≤ 4 * X) (hX : 0 ≤ X)
    (hN : 1 ≤ Nr) (hY : 1 ≤ Y) (hb' : C * k ^ 3 * Nr * Q ^ 4 * X * Y ≤ b')
    (hIb : Yb * Nr * La * b' / k ≤ Ib) :
    12 * c + (N1 + 1) * (Cm * k * N1 * Q * c) ≤ (2 * Ib / b') * (b' / (2 * Q)) / 4 := by
  have hQ0 : 0 < Q := by linarith
  have hk0 : 0 < k := by linarith
  have hC1 : 1 ≤ C := by linarith
  have hN10 : 0 < N1 := by linarith
  have hR : (2 * Ib / b') * (b' / (2 * Q)) / 4 = Ib / (4 * Q) := by
    field_simp
  rw [hR, le_div_iff₀ (by positivity)]

  have hW : 1 ≤ k * N1 ^ 2 * Q :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hk (one_le_pow₀ hN1)) hQ
  have a1 : 12 * c ≤ 12 * c * (k * N1 ^ 2 * Q) := le_mul_of_one_le_right (by linarith) hW
  have a2 : (N1 + 1) * (Cm * k * N1 * Q * c) ≤ (2 * N1) * (Cm * k * N1 * Q * c) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have a3 : (12 + 2 * Cm) * (k * N1 ^ 2 * Q) * c ≤ (12 + 2 * Cm) * (k * N1 ^ 2 * Q) * (4 * X) :=
    mul_le_mul_of_nonneg_left hc (by positivity)
  have hL : 12 * c + (N1 + 1) * (Cm * k * N1 * Q * c) ≤ (48 + 8 * Cm) * (k * N1 ^ 2 * Q * X) := by
    linarith
  have hV : 0 ≤ k * N1 ^ 2 * Q ^ 2 * X := by positivity
  have hL2 : (12 * c + (N1 + 1) * (Cm * k * N1 * Q * c)) * (4 * Q) ≤ C * (k * N1 ^ 2 * Q ^ 2 * X) := by
    have b1 := mul_le_mul_of_nonneg_right hL (by positivity : 0 ≤ 4 * Q)
    have b2 := mul_le_mul_of_nonneg_right hC hV
    linarith

  have hq4 : Q ^ 2 ≤ Q ^ 4 := pow_le_pow_right₀ hQ (by norm_num)
  have hq : Q ^ 2 ≤ Nr * Q ^ 4 * Y := by
    have h2 : Q ^ 4 ≤ Nr * Q ^ 4 := le_mul_of_one_le_left (by positivity) hN
    have h3 : Nr * Q ^ 4 ≤ Nr * Q ^ 4 * Y := le_mul_of_one_le_right (by positivity) hY
    linarith
  have hb2 : C * k ^ 3 * Q ^ 2 * X ≤ b' := by
    have h4 : C * k ^ 3 * Q ^ 2 * X ≤ C * k ^ 3 * (Nr * Q ^ 4 * Y) * X :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq (by positivity)) hX
    linarith
  have hIb' : Yb * Nr * La * b' ≤ Ib * k := (div_le_iff₀ hk0).mp hIb
  have hYN : 1 ≤ Yb * Nr := one_le_mul_of_one_le_of_one_le (by linarith) hN
  have hLa0 : 0 ≤ La := le_trans (by positivity) hLa
  have c1 : N1 ^ 2 * b' ≤ Yb * Nr * La * b' := by
    have d1 : N1 ^ 2 * b' ≤ La * b' := mul_le_mul_of_nonneg_right hLa hb.le
    have d2 : La * b' ≤ (Yb * Nr) * (La * b') := le_mul_of_one_le_left (by positivity) hYN
    linarith
  have c2 : N1 ^ 2 * (C * k ^ 3 * Q ^ 2 * X) ≤ N1 ^ 2 * b' := mul_le_mul_of_nonneg_left hb2 (by positivity)
  have c3 : C * (k * N1 ^ 2 * Q ^ 2 * X) * k ≤ C * (k * N1 ^ 2 * Q ^ 2 * X) * k * k :=
    le_mul_of_one_le_right (by positivity) hk
  have c4 : C * (k * N1 ^ 2 * Q ^ 2 * X) * k ≤ Ib * k := by linarith
  have c5 : C * (k * N1 ^ 2 * Q ^ 2 * X) ≤ Ib := le_of_mul_le_mul_right c4 hk0
  linarith

end RoomIProof

end Formalism.CountingSumsFrames
