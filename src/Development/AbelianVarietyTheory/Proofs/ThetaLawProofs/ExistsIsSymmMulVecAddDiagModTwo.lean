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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory

theorem exists_isSymm_mulVec_add_diag_mod_two :
    ∀ (g : ℕ) (n n' : Fin g → ℤ), Even (n ⬝ᵥ n') →
      ∃ S : Matrix (Fin g) (Fin g) ℤ, S.IsSymm ∧
        ∀ i, (2 : ℤ) ∣ (S.mulVec n) i + S i i - n' i := by
  intro g n n' h
  by_cases hall : ∀ i, Even (n i)
  · refine ⟨Matrix.diagonal n', Matrix.isSymm_diagonal _, fun i => ?_⟩
    obtain ⟨k, hk⟩ := hall i
    rw [Matrix.mulVec_diagonal, Matrix.diagonal_apply_eq, hk]
    exact ⟨n' i * k, by ring⟩
  · obtain ⟨p, hp⟩ := not_forall.mp hall
    obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp hp
    obtain ⟨m, hm⟩ := h
    refine ⟨Matrix.of fun i j => (if i = p then n' j else 0) + (if j = p then n' i else 0),
      ?_, fun i => ?_⟩
    · ext i j
      simp only [Matrix.transpose_apply, Matrix.of_apply]
      ring
    · have hm' : ∑ j, n' j * n j = m + m := by
        rw [← hm]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      have h2 : ∑ j, (if j = p then n' i else 0) * n j = n' i * n p := by
        simp
      by_cases hi : i = p
      · subst hi
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
          if_true, hm', h2, hk]
        exact ⟨m + n' i * k + n' i, by ring⟩
      · simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
          if_neg hi, h2, hk, zero_mul, Finset.sum_const_zero]
        exact ⟨n' i * k, by ring⟩

end GlobalTheory
