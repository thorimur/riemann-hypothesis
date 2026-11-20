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

namespace Bl.ProductIdentities

private lemma prod_erase_one_perm_apply_eq_zero {n : Type} [Fintype n] [DecidableEq n] (σ : Equiv.Perm n) (hσ : σ ≠ 1)
    (k : n) : ∏ j ∈ Finset.univ.erase k, (1 : Matrix n n ℂ) (σ j) j = 0 := by
  have hex : ∃ j, j ≠ k ∧ σ j ≠ j := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    apply hσ
    ext x
    simp only [Equiv.Perm.coe_one, id_eq]
    by_cases hx : x = k
    · subst hx
      by_contra hk
      exact hk (σ.injective (h (σ x) hk))
    · exact h x hx
  obtain ⟨j, hjk, hj⟩ := hex
  apply Finset.prod_eq_zero (i := j) (Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ _⟩)
  simp [hj]

theorem goal1 :
  ∀ {n : Type} [inst : Fintype.{0} n] [inst_1 : DecidableEq.{1} n] (A : Real → Matrix.{0, 0, 0} n n Complex)
  (A' : Matrix.{0, 0, 0} n n Complex),
  Eq.{1} (A 0) 1 →
    (∀ (i j : n), HasDerivAt.{0, 0} (fun (t : Real) ↦ A t i j) (A' i j) 0) →
      HasDerivAt.{0, 0} (fun (t : Real) ↦ Matrix.det.{0, 0} (A t)) (Matrix.trace.{0, 0} A') 0 := by
  intro n _ _ A A' h0 hd
  have key : ∀ σ : Equiv.Perm n, HasDerivAt
      (fun t : ℝ => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i)
      (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∑ k, (∏ j ∈ Finset.univ.erase k, A 0 (σ j) j) • A' (σ k) k) 0 := by
    intro σ
    apply HasDerivAt.const_mul
    exact HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun i t => A t (σ i) i)
      (f' := fun i => A' (σ i) i) (fun k _ => hd (σ k) k)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ => key σ)
  have hfun : (fun t : ℝ => Matrix.det (A t)) =
      fun t => ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i := by
    funext t
    exact Matrix.det_apply' _
  rw [hfun]
  refine hsum.congr_deriv ?_
  rw [Finset.sum_eq_single (1 : Equiv.Perm n)]
  · rw [h0]
    simp [Matrix.trace, Matrix.one_apply]
  · intro σ _ hσ
    rw [h0, Finset.sum_eq_zero (fun k _ => by rw [prod_erase_one_perm_apply_eq_zero σ hσ k, zero_smul]), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Bl.ProductIdentities
