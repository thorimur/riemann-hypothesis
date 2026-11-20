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

open Finset Matrix
open NormedSpace

namespace Bl.MovedPointExistence

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private lemma exists_moved (σ : Equiv.Perm ι) (hσ : σ ≠ 1) (i : ι) :
    ∃ j, j ≠ i ∧ σ j ≠ j := by
  obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
    by_contra hc
    push Not at hc
    exact hσ (Equiv.ext fun x => by simpa using hc x)
  by_cases hi : σ i = i
  · refine ⟨k, ?_, hk⟩
    rintro rfl
    exact hk hi
  · refine ⟨σ i, hi, ?_⟩
    intro h2
    exact hi (σ.injective h2)

theorem goal1 (A : ℝ → Matrix ι ι ℂ) (A' : Matrix ι ι ℂ) (h0 : A 0 = 1)
    (h : ∀ i j, HasDerivAt (fun t => A t i j) (A' i j) 0) :
    HasDerivAt (fun t => (A t).det) A'.trace 0 := by
  have hfun : (fun t => (A t).det) =
      fun t => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i := by
    funext t
    exact Matrix.det_apply' (A t)
  rw [hfun]
  have key : ∀ σ : Equiv.Perm ι,
      HasDerivAt (fun t => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i)
        (((Equiv.Perm.sign σ : ℤ) : ℂ) *
          ∑ i, (∏ j ∈ univ.erase i, A 0 (σ j) j) • A' (σ i) i) 0 := by
    intro σ
    exact (HasDerivAt.fun_finsetProd (u := univ) (fun i _ => h (σ i) i)).const_mul _
  have hs := HasDerivAt.fun_sum (u := univ) (fun σ _ => key σ)
  refine hs.congr_deriv ?_
  rw [h0, Finset.sum_eq_single (1 : Equiv.Perm ι)]
  · simp only [Matrix.trace, Matrix.diag_apply, Equiv.Perm.sign_one, Units.val_one, Int.cast_one,
      one_mul, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.prod_eq_one (fun j _ => ?_), one_mul]
    · rfl
    · rw [Equiv.Perm.one_apply, Matrix.one_apply_eq]
  · intro σ _ hσ
    rw [Finset.sum_eq_zero, mul_zero]
    intro i _
    obtain ⟨j, hji, hj⟩ := exists_moved σ hσ i
    have hz : ∏ l ∈ univ.erase i, (1 : Matrix ι ι ℂ) (σ l) l = 0 :=
      Finset.prod_eq_zero (i := j) (by simp [hji]) (Matrix.one_apply_ne hj)
    rw [hz, zero_smul]
  · intro hn
    exact absurd (Finset.mem_univ _) hn

end Bl.MovedPointExistence
