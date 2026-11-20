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

namespace GlobalTheory.EvalNatCastZero

open Polynomial

theorem eq_zero_of_eval_natCast_add {R : Type} [CommRing R]
    (hR : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R)) (n : ℕ) (F : Polynomial R) (hF : F.natDegree ≤ n)
    (m : ℕ) (h : ∀ k : ℕ, Polynomial.eval ((m + k : ℕ) : R) F = 0) : F = 0 := by
  nontriviality R
  induction n generalizing F m with
  | zero =>
    have h0 := h 0
    rw [eq_C_of_natDegree_le_zero hF] at h0 ⊢
    rw [eval_C] at h0
    rw [h0, C_0]
  | succ n ih =>
    have hroot : F.IsRoot (m : R) := by simpa using h 0
    have hfac : (X - C (m : R)) * (F /ₘ (X - C (m : R))) = F :=
      mul_divByMonic_eq_iff_isRoot.2 hroot
    have hdeg : (F /ₘ (X - C (m : R))).natDegree ≤ n := by
      rw [natDegree_divByMonic F (monic_X_sub_C _), natDegree_X_sub_C]
      omega
    have hG : F /ₘ (X - C (m : R)) = 0 := by
      refine ih _ hdeg (m + 1) fun k => ?_
      have h1 := h (k + 1)
      rw [← hfac, eval_mul, eval_sub, eval_X, eval_C] at h1
      have e1 : ((m + (k + 1) : ℕ) : R) - (m : R) = ((k + 1 : ℕ) : R) := by push_cast; ring
      have e2 : m + 1 + k = m + (k + 1) := by ring
      rw [e1] at h1
      rw [e2]
      exact (hR (k + 1) (Nat.succ_ne_zero k)).mul_right_eq_zero.1 h1
    rw [← hfac, hG, mul_zero]

end GlobalTheory.EvalNatCastZero
