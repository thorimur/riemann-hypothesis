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
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

theorem UpperTheory.Reformulated.B.Qh34.aux1.{u_1} :
    ∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K],
      ∑ x : NumberField.InfinitePlace K,
          (↑x.mult : ℝ) *
            ((NumberField.InfinitePlace.Completion.extensionEmbedding x : x.Completion → ℂ)
                ((0 : NumberField.InfiniteAdeleRing K) x)).re =
        (0 : ℝ) := by
  intro K _ _
  refine Finset.sum_eq_zero fun w _ => ?_
  have h : (0 : NumberField.InfiniteAdeleRing K) w = 0 := rfl
  rw [h, map_zero, Complex.zero_re, mul_zero]

theorem UpperTheory.Reformulated.B.Qh34.aux2.{u_1} :
    ∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] (x y : NumberField.InfiniteAdeleRing K),
      ∑ w : NumberField.InfinitePlace K,
          (↑w.mult : ℝ) * ((NumberField.InfinitePlace.Completion.extensionEmbedding w : w.Completion → ℂ) ((x + y) w)).re =
        ∑ w : NumberField.InfinitePlace K,
            (↑w.mult : ℝ) * ((NumberField.InfinitePlace.Completion.extensionEmbedding w : w.Completion → ℂ) (x w)).re +
          ∑ w : NumberField.InfinitePlace K,
            (↑w.mult : ℝ) * ((NumberField.InfinitePlace.Completion.extensionEmbedding w : w.Completion → ℂ) (y w)).re := by
  intro K _ _ x y
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h : (x + y) w = x w + y w := rfl
  rw [h, map_add, Complex.add_re, mul_add]

noncomputable def UpperTheory.Reformulated.B.Qh34.infiniteTrace.{u_1} :
    (K : Type u_1) → [inst : Field K] → [NumberField K] → NumberField.InfiniteAdeleRing K →+ ℝ :=
    fun (K : Type u_1) [Field K] [NumberField K] ↦
      {
        toFun := fun (x : NumberField.InfiniteAdeleRing K) ↦
          ∑ w : NumberField.InfinitePlace K,
            (↑w.mult : ℝ) * ((NumberField.InfinitePlace.Completion.extensionEmbedding w : w.Completion → ℂ) (x w)).re,
        map_zero' := UpperTheory.Reformulated.B.Qh34.aux1 K, map_add' := UpperTheory.Reformulated.B.Qh34.aux2 K : NumberField.InfiniteAdeleRing K →+ ℝ }

theorem UpperTheory.Reformulated.B.Qh34.infiniteTrace_algebraMap.{u_1} :
    ∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] (k : K),
      (UpperTheory.Reformulated.B.Qh34.infiniteTrace K : NumberField.InfiniteAdeleRing K → ℝ)
          ((Algebra.algebraMap K (NumberField.InfiniteAdeleRing K) : K → NumberField.InfiniteAdeleRing K) k) =
        (↑((Algebra.trace ℚ K : K → ℚ) k) : ℝ) := by
  classical
  intro K _ _ k
  have h1 : ((Algebra.trace ℚ K k : ℚ) : ℝ) = ∑ φ : K →+* ℂ, (φ k).re := by
    have h := trace_eq_sum_embeddings ℂ (K := ℚ) (L := K) (x := k)
    have h' : ∑ φ : K →+* ℂ, φ k = ∑ σ : K →ₐ[ℚ] ℂ, σ k :=
      Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun _ => rfl)
    rw [← Complex.re_sum, h', ← h]
    simp
  rw [h1, ← Finset.sum_fiberwise Finset.univ NumberField.InfinitePlace.mk]
  change ∑ w : NumberField.InfinitePlace K, (↑w.mult : ℝ) *
    (NumberField.InfinitePlace.Completion.extensionEmbedding w
      (algebraMap K (NumberField.InfiniteAdeleRing K) k w)).re = _
  refine Finset.sum_congr rfl fun w _ => ?_
  have h2 : NumberField.InfinitePlace.Completion.extensionEmbedding w
      (algebraMap K (NumberField.InfiniteAdeleRing K) k w) = w.embedding k := by
    simp
  have h3 : ∀ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => NumberField.InfinitePlace.mk φ = w),
      (φ k).re = (w.embedding k).re := by
    intro φ hφ
    rw [← (Finset.mem_filter.1 hφ).2]
    rcases NumberField.InfinitePlace.embedding_mk_eq φ with h | h
    · rw [h]
    · rw [h, NumberField.ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
  rw [h2, Finset.sum_congr rfl h3, Finset.sum_const, NumberField.InfinitePlace.card_filter_mk_eq,
    nsmul_eq_mul]
