import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
open NumberField

namespace GlobalTheory

open Classical in

theorem mixedSpace_trace_eq (F : Type) [Field F] [NumberField F]
    (x : mixedEmbedding.mixedSpace F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) x =
      ∑ w, x.1 w + ∑ w, 2 * (x.2 w).re := by
  rw [Algebra.trace_eq_matrix_trace (mixedEmbedding.stdBasis F), Matrix.trace,
    Fintype.sum_sum_type, Fintype.sum_prod_type]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul,
      mixedEmbedding.stdBasis_apply_isReal]
    simp [mixedEmbedding.stdBasis]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [Fin.sum_univ_two, Matrix.diag_apply, Matrix.diag_apply,
      Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
      mixedEmbedding.stdBasis_apply_isComplex_fst, mixedEmbedding.stdBasis_apply_isComplex_snd]
    simp [mixedEmbedding.stdBasis, two_mul]

open Classical in

theorem mixedSpace_traceForm_nondegenerate :
    ∀ (F : Type) [Field F] [NumberField F] (ξ : mixedEmbedding.mixedSpace F),
    (∀ η : mixedEmbedding.mixedSpace F,
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (ξ * η) = 0) → ξ = 0 := by
  intro F _ _ ξ h
  have h0 := h (ξ.1, fun w => (starRingEnd ℂ) (ξ.2 w))
  rw [mixedSpace_trace_eq] at h0
  simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, Complex.mul_conj, Complex.ofReal_re] at h0
  have h1 : 0 ≤ ∑ w, ξ.1 w * ξ.1 w := Finset.sum_nonneg fun w _ => mul_self_nonneg _
  have h2 : 0 ≤ ∑ w, 2 * Complex.normSq (ξ.2 w) :=
    Finset.sum_nonneg fun w _ => mul_nonneg (by norm_num) (Complex.normSq_nonneg _)
  have h3 : ∑ w, ξ.1 w * ξ.1 w = 0 := by linarith
  have h4 : ∑ w, 2 * Complex.normSq (ξ.2 w) = 0 := by linarith
  rw [Finset.sum_eq_zero_iff_of_nonneg fun w _ => mul_self_nonneg _] at h3
  rw [Finset.sum_eq_zero_iff_of_nonneg fun w _ =>
    mul_nonneg (by norm_num) (Complex.normSq_nonneg _)] at h4
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · exact mul_self_eq_zero.1 (h3 w (Finset.mem_univ _))
  · have := h4 w (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.1 (by linarith)

end GlobalTheory
