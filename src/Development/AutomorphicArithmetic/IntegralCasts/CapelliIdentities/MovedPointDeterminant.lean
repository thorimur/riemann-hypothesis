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

private theorem UpperTheory.Reformulated.B.MovedPointDeterminant.exists_moved_ne {a : ℕ} {σ : Equiv.Perm (Fin a)} (hσ : σ ≠ 1)
    (i : Fin a) : ∃ j, j ≠ i ∧ σ j ≠ j := by
  by_contra h
  push Not at h
  apply hσ
  ext1 j
  by_cases hj : j = i
  · subst hj
    by_contra hne
    exact hne (σ.injective (h _ hne))
  · exact h j hj

theorem UpperTheory.Reformulated.B.MovedPointDeterminant.cv_det :
    ∀ {a : ℕ} {m : ℝ → Matrix (Fin a) (Fin a) ℂ}
    {Y : Matrix (Fin a) (Fin a) ℂ},
    m (0 : ℝ) = (1 : Matrix (Fin a) (Fin a) ℂ) →
      (∀ (i j : Fin a), HasDerivAt (fun (s : ℝ) ↦ m s i j) (Y i j) (0 : ℝ)) →
        HasDerivAt (fun (s : ℝ) ↦ (m s).det) (∑ i : Fin a, Y i i) (0 : ℝ) := by
  intro a m Y h0 hd
  have key : HasDerivAt
      (fun s : ℝ ↦ ∑ σ : Equiv.Perm (Fin a), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, m s (σ i) i)
      (∑ σ : Equiv.Perm (Fin a), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ i, (∏ j ∈ Finset.univ.erase i, m 0 (σ j) j) • Y (σ i) i) 0 :=
    HasDerivAt.fun_sum fun σ _ ↦
      (HasDerivAt.fun_finsetProd (f := fun i s ↦ m s (σ i) i)
        (fun i _ ↦ hd (σ i) i)).const_mul _
  have hval : (∑ σ : Equiv.Perm (Fin a), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ i, (∏ j ∈ Finset.univ.erase i, m 0 (σ j) j) • Y (σ i) i) = ∑ i, Y i i := by
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin a))]
    · simp [h0]
    · intro σ _ hσ
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun i _ ↦ ?_)
      obtain ⟨j, hj, hm⟩ := UpperTheory.Reformulated.B.MovedPointDeterminant.exists_moved_ne hσ i
      rw [Finset.prod_eq_zero (i := j) (by simp [hj]) (by rw [h0, Matrix.one_apply_ne hm]),
        zero_smul]
    · simp
  rw [hval] at key
  simpa only [Matrix.det_apply'] using key
