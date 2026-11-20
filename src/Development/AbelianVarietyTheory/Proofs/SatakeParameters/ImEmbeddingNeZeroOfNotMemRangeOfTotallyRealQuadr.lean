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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
open NumberField

namespace GlobalTheory

theorem im_embedding_ne_zero_of_not_mem_range_of_totallyReal_quadratic
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [IsTotallyComplex E] [Algebra.IsQuadraticExtension F E]
    (w : InfinitePlace E) (θ : E) (hθ : θ ∉ Set.range (algebraMap F E)) :
    (w.embedding θ).im ≠ 0 := by
  intro h
  set φ := w.embedding with hφ
  have hF : ∀ c : F, (φ (algebraMap F E c)).im = 0 := by
    intro c
    have hr : ComplexEmbedding.IsReal (φ.comp (algebraMap F E)) :=
      InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)
    have := ComplexEmbedding.isReal_iff.1 hr
    have h2 := RingHom.congr_fun this c
    exact Complex.conj_eq_iff_im.1 h2
  have hli : LinearIndependent F ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hθ
      refine ⟨-(s / t), ?_⟩
      have : t • θ = -(s • (1 : E)) := eq_neg_of_add_eq_zero_right hst
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at this
      have ht' : algebraMap F E t ≠ 0 := by simpa using ht
      rw [map_neg, map_div₀]
      field_simp
      rw [mul_comm] at this
      linear_combination -this
  have hspan : Submodule.span F (Set.range ![(1 : E), θ]) = ⊤ := by
    apply hli.span_eq_top_of_card_eq_finrank
    simp [Algebra.IsQuadraticExtension.finrank_eq_two F E]
  have hall : ∀ z : E, (φ z).im = 0 := by
    intro z
    have hz : z ∈ Submodule.span F (Set.range ![(1 : E), θ]) := hspan ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hz
    rw [← hc, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Algebra.smul_def,
      mul_one, map_add, map_mul, Complex.add_im, Complex.mul_im, hF, h, zero_mul, mul_zero,
      add_zero]
  have hreal : ComplexEmbedding.IsReal φ := by
    rw [ComplexEmbedding.isReal_iff]
    ext1 z
    exact Complex.conj_eq_iff_im.2 (hall z)
  exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
    (InfinitePlace.isReal_iff.2 hreal)

example : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] [Algebra.IsQuadraticExtension F E] (w : InfinitePlace E) (θ : E), θ ∉ Set.range (algebraMap F E) → (w.embedding θ).im ≠ 0 :=
  im_embedding_ne_zero_of_not_mem_range_of_totallyReal_quadratic

end GlobalTheory
