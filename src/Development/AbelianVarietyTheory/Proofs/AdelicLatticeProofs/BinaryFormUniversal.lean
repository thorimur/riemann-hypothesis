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

universe u_1

namespace GlobalTheory.BinaryFormUniversal

open Polynomial

theorem binary_form_universal {k : Type u_1} [Field k] [Finite k] {a n : k}
    (hD : a ^ (2 : ℕ) - (4 : k) * n ≠ (0 : k)) (u : k) :
    ∃ (r : k) (s : k), r ^ (2 : ℕ) + a * r * s + n * s ^ (2 : ℕ) = u := by
  classical
  by_cases h2 : ringChar k = 2
  · obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two h2 u
    exact ⟨r, 0, by rw [hr]; ring⟩
  · letI := Fintype.ofFinite k
    have hodd : Fintype.card k % 2 = 1 := FiniteField.odd_card_of_char_ne_two h2
    have h2' : (2 : k) ≠ 0 := Ring.two_ne_zero h2
    have hD' : -(a ^ 2 - 4 * n) ≠ 0 := neg_ne_zero.mpr hD
    have hf : degree (X ^ 2 : k[X]) = 2 := by simp
    have hg : degree (C (-(a ^ 2 - 4 * n)) * X ^ 2 + C 0 * X + C (-(4 * u)) : k[X]) = 2 :=
      degree_quadratic hD'
    obtain ⟨x, s, h⟩ := FiniteField.exists_root_sum_quadratic hf hg hodd
    simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C] at h
    refine ⟨(x - a * s) / 2, s, ?_⟩
    field_simp
    linear_combination h

end GlobalTheory.BinaryFormUniversal
