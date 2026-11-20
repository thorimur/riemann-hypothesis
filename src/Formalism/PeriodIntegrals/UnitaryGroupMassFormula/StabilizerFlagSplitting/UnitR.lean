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
import Mathlib.RingTheory.PiTensorProduct
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

namespace PI.StabSplit.Alg

variable {R : Type*} [Ring R]

theorem decomp (h P : R) (hPP : P * P = P) (hU : P * h * (1 - P) = 0) :
    (h * P + (1 - P)) * (h * (1 - P) + P) = h := by
  have r : P * P - P = 0 := sub_eq_zero.mpr hPP
  have e : (h * P + (1 - P)) * (h * (1 - P) + P) - h =
      h * (P * h * (1 - P)) + h * (P * P - P) - P * h * (1 - P) - (P * P - P) := by
    noncomm_ring
  have z : h * (P * h * (1 - P)) + h * (P * P - P) - P * h * (1 - P) - (P * P - P) = 0 := by
    simp only [hU, r, mul_zero, add_zero, sub_zero]
  exact sub_eq_zero.mp (e.trans z)

theorem uniq (h P ρ κ : R) (hρκ : ρ * κ = h) (hρ : ρ * (1 - P) = 1 - P) (hκ : κ * P = P)
    (hκU : P * κ * (1 - P) = 0) :
    ρ = h * P + (1 - P) ∧ κ = h * (1 - P) + P := by
  have a : ρ * κ - h = 0 := sub_eq_zero.mpr hρκ
  have b : ρ * (1 - P) - (1 - P) = 0 := sub_eq_zero.mpr hρ
  have c : κ * P - P = 0 := sub_eq_zero.mpr hκ
  constructor
  · have e : ρ - (h * P + (1 - P)) = (ρ * κ - h) * P - ρ * (κ * P - P) + (ρ * (1 - P) - (1 - P)) := by
      noncomm_ring
    have z : (ρ * κ - h) * P - ρ * (κ * P - P) + (ρ * (1 - P) - (1 - P)) = 0 := by
      simp only [a, b, c, mul_zero, zero_mul, add_zero, sub_zero]
    exact sub_eq_zero.mp (e.trans z)
  · have e : κ - (h * (1 - P) + P) = (κ * P - P) + P * κ * (1 - P) + (ρ * κ - h) * (1 - P)
        - ρ * (P * κ * (1 - P)) - (ρ * (1 - P) - (1 - P)) * κ * (1 - P) := by
      noncomm_ring
    have z : (κ * P - P) + P * κ * (1 - P) + (ρ * κ - h) * (1 - P)
        - ρ * (P * κ * (1 - P)) - (ρ * (1 - P) - (1 - P)) * κ * (1 - P) = 0 := by
      simp only [a, b, c, hκU, mul_zero, zero_mul, add_zero, sub_zero]
    exact sub_eq_zero.mp (e.trans z)

theorem comm (P ρ κ : R) (hρ : ρ * (1 - P) = 1 - P) (hκ : κ * P = P)
    (hρM : (1 - P) * ρ * P = 0) (hκU : P * κ * (1 - P) = 0) : ρ * κ = κ * ρ := by
  have b : ρ * (1 - P) - (1 - P) = 0 := sub_eq_zero.mpr hρ
  have c : κ * P - P = 0 := sub_eq_zero.mpr hκ
  have e : ρ * κ - κ * ρ = ρ * (κ * P - P) + ρ * (P * κ * (1 - P)) - P * κ * (1 - P)
      + (ρ * (1 - P) - (1 - P)) * κ * (1 - P) + (1 - P) * ρ * P - (κ * P - P) * ρ * P
      - κ * ((1 - P) * ρ * P) - κ * (ρ * (1 - P) - (1 - P)) := by
    noncomm_ring
  have z : ρ * (κ * P - P) + ρ * (P * κ * (1 - P)) - P * κ * (1 - P)
      + (ρ * (1 - P) - (1 - P)) * κ * (1 - P) + (1 - P) * ρ * P - (κ * P - P) * ρ * P
      - κ * ((1 - P) * ρ * P) - κ * (ρ * (1 - P) - (1 - P)) = 0 := by
    simp only [b, c, hρM, hκU, mul_zero, zero_mul, add_zero, sub_zero]
  exact sub_eq_zero.mp (e.trans z)

theorem nilp (P g : R) (m : ℕ) (hPP : P * P = P) (hgQ : (g - 1) * (1 - P) = 0)
    (hgM : (1 - P) * g * P = 0) (hm : (g - 1) ^ m * P = 0) : (g - 1) ^ (m + 1) = 0 := by
  have r : P * P - P = 0 := sub_eq_zero.mpr hPP
  have h1 : (g - 1) * P = P * ((g - 1) * P) := by
    have e : (g - 1) * P - P * ((g - 1) * P) = (1 - P) * g * P + (P * P - P) := by noncomm_ring
    rw [hgM, r, add_zero] at e
    exact sub_eq_zero.mp e
  have h2 : g - 1 = (g - 1) * P := by
    have e : (g - 1) - (g - 1) * P = (g - 1) * (1 - P) := by noncomm_ring
    rw [hgQ] at e
    exact sub_eq_zero.mp e
  calc (g - 1) ^ (m + 1) = (g - 1) ^ m * (g - 1) := pow_succ _ _
    _ = (g - 1) ^ m * ((g - 1) * P) := by rw [← h2]
    _ = (g - 1) ^ m * (P * ((g - 1) * P)) := by rw [← h1]
    _ = ((g - 1) ^ m * P) * ((g - 1) * P) := (mul_assoc _ _ _).symm
    _ = 0 := by rw [hm, zero_mul]

variable [StarRing R]

theorem unitK (H P h : R) (hH : star H = H) (hPH : star P * H = H * P) (hPP : P * P = P)
    (hh : star h * H * h = H) (hU : P * h * (1 - P) = 0) :
    star (h * (1 - P) + P) * H * (h * (1 - P) + P) = H := by
  have r1 : star P * H - H * P = 0 := sub_eq_zero.mpr hPH
  have r2 : P * P - P = 0 := sub_eq_zero.mpr hPP
  have r3 : star h * H * h - H = 0 := sub_eq_zero.mpr hh
  have r5 : (1 - star P) * (star h * star P) = 0 := by
    simpa only [star_mul, star_sub, star_one, star_zero] using congrArg star hU
  have e : star (h * (1 - P) + P) * H * (h * (1 - P) + P) - H =
      H * (P * P - P) + H * (P * P - P) - (star P * H - H * P) * (1 - P)
      + (1 - star P) * (star h * H * h - H) * (1 - P) + (1 - star P) * (star h * star P) * H
      - (1 - star P) * star h * (star P * H - H * P) + H * (P * h * (1 - P))
      + (star P * H - H * P) * h * (1 - P) + (star P * H - H * P) * P := by
    simp only [star_add, star_mul, star_sub, star_one]
    noncomm_ring
  have z : H * (P * P - P) + H * (P * P - P) - (star P * H - H * P) * (1 - P)
      + (1 - star P) * (star h * H * h - H) * (1 - P) + (1 - star P) * (star h * star P) * H
      - (1 - star P) * star h * (star P * H - H * P) + H * (P * h * (1 - P))
      + (star P * H - H * P) * h * (1 - P) + (star P * H - H * P) * P = 0 := by
    simp only [r1, r2, r3, r5, hU, mul_zero, zero_mul, add_zero, sub_zero]
  exact sub_eq_zero.mp (e.trans z)

end PI.StabSplit.Alg
