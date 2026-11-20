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
import Mathlib.Tactic.ENatToNat
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

namespace GlobalTheory.DetDerivativeAtOne

open Equiv Finset

theorem hasDerivAt_det_of_one {n : Type} [Fintype n] [DecidableEq n]
    (A : ℝ → Matrix n n ℂ) (A' : Matrix n n ℂ) (h0 : A (0 : ℝ) = (1 : Matrix n n ℂ))
    (hd : ∀ (i j : n), HasDerivAt (fun (t : ℝ) ↦ A t i j) (A' i j) (0 : ℝ)) :
    HasDerivAt (fun (t : ℝ) ↦ Matrix.det (A t)) (Matrix.trace A') (0 : ℝ) := by
  have hfun : (fun t : ℝ ↦ Matrix.det (A t)) =
      fun t ↦ ∑ σ : Perm n, ((Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i :=
    funext fun t ↦ Matrix.det_apply' _
  rw [hfun]
  have hσ : ∀ σ : Perm n, HasDerivAt (fun t : ℝ ↦ ∏ i, A t (σ i) i)
      (∑ i, (∏ j ∈ univ.erase i, A 0 (σ j) j) • A' (σ i) i) 0 :=
    fun σ ↦ HasDerivAt.fun_finsetProd (fun i _ ↦ hd (σ i) i)
  have hsum := HasDerivAt.fun_sum (u := (univ : Finset (Perm n)))
    (fun σ _ ↦ (hσ σ).const_mul ((Perm.sign σ : ℤ) : ℂ))
  refine hsum.congr_deriv (Eq.symm ?_)
  rw [h0]
  rw [Finset.sum_eq_single (1 : Perm n)]
  · simp [Matrix.trace, Perm.one_apply, Matrix.one_apply]
  · intro σ _ hσ1
    have hz : ∀ i, (∏ j ∈ univ.erase i, (1 : Matrix n n ℂ) (σ j) j) = 0 := by
      intro i
      obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
        by_contra hc
        push Not at hc
        exact hσ1 (Equiv.ext hc)
      by_cases hki : k = i
      · subst hki
        apply Finset.prod_eq_zero (i := σ k)
        · simp [hk]
        · have : σ (σ k) ≠ σ k := fun h ↦ hk (σ.injective h)
          simp [Matrix.one_apply_ne this]
      · apply Finset.prod_eq_zero (i := k)
        · simp [hki]
        · simp [Matrix.one_apply_ne hk]
    simp [hz]
  · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.DetDerivativeAtOne
