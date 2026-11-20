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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

open Finset NumberField Module
open scoped ComplexConjugate nonZeroDivisors

namespace Bl.FiberEquations

private lemma fiber_eq {E : Type} [Field E] (w : InfinitePlace E) [DecidableEq (InfinitePlace E)]
    [DecidableEq (E →+* ℂ)] [Fintype (E →+* ℂ)] :
    ({φ | InfinitePlace.mk φ = w} : Finset (E →+* ℂ)) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
  ext φ
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  conv_lhs => rw [← InfinitePlace.mk_embedding w, InfinitePlace.mk_eq_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right
      rw [← h, ComplexEmbedding.involutive_conjugate E φ]
  · rintro (h | h)
    · exact Or.inl h
    · right
      rw [h, ComplexEmbedding.involutive_conjugate E]

theorem goal1 (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (x : E) :
    ((Algebra.trace ℚ E x : ℚ) : ℝ) = ∑ w : InfinitePlace E, 2 * (w.embedding x).re := by
  classical
  have h1 : ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ φ : E →+* ℂ, φ x := by
    have h := trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := x)
    rw [eq_ratCast] at h
    rw [h]
    exact Fintype.sum_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm _ _ (fun σ => rfl)
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, h1, Complex.ofReal_sum,
    ← Finset.sum_fiberwise univ (fun φ : E →+* ℂ => InfinitePlace.mk φ) (fun φ => φ x)]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
    intro h
    exact IsTotallyComplex.complexEmbedding_not_isReal w.embedding
      (ComplexEmbedding.isReal_iff.mpr h.symm)
  rw [fiber_eq w, Finset.sum_pair hne, ComplexEmbedding.conjugate_coe_eq, Complex.add_conj]

end Bl.FiberEquations
