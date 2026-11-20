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
import Mathlib.Topology.Sheaves.Init
open NumberField

namespace GlobalTheory

theorem infinitePlace_eq_of_embedding_comp_algebraMap_eq (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E]
    [Algebra.IsQuadraticExtension F E] (w₁ w₂ : InfinitePlace E)
    (h : w₁.embedding.comp (algebraMap F E) = w₂.embedding.comp (algebraMap F E)) : w₁ = w₂ := by
  classical
  set τ : F →+* ℂ := w₁.embedding.comp (algebraMap F E) with hτ
  have hτreal : ComplexEmbedding.IsReal τ := by
    have := IsTotallyReal.isReal (InfinitePlace.mk τ)
    exact InfinitePlace.isReal_mk_iff.mp this
  letI : Algebra F ℂ := τ.toAlgebra
  have mkAlg : ∀ σ : E →+* ℂ, σ.comp (algebraMap F E) = τ → ∃ a : E →ₐ[F] ℂ, (a : E →+* ℂ) = σ :=
    fun σ hσ => ⟨{ σ with
      commutes' := fun r => by
        change σ (algebraMap F E r) = τ r
        rw [← hσ]; rfl }, rfl⟩
  obtain ⟨a, ha⟩ := mkAlg w₁.embedding rfl
  obtain ⟨b, hb⟩ := mkAlg (ComplexEmbedding.conjugate w₁.embedding) (by
    ext r
    have := RingHom.congr_fun hτreal r
    simp only [RingHom.comp_apply, ComplexEmbedding.conjugate_coe_eq, Function.comp_apply]
    simpa [ComplexEmbedding.conjugate_coe_eq, hτ] using this)
  obtain ⟨c, hc⟩ := mkAlg w₂.embedding h.symm
  have hab : a ≠ b := by
    intro hab
    have hc1 : ¬ ComplexEmbedding.IsReal w₁.embedding := by
      rw [← InfinitePlace.isReal_iff]
      exact InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w₁)
    apply hc1
    rw [ComplexEmbedding.isReal_iff, ← hb, ← ha, hab]
  have hcard : Fintype.card (E →ₐ[F] ℂ) = 2 := by
    rw [AlgHom.card, Algebra.IsQuadraticExtension.finrank_eq_two]
  have hcab : c = a ∨ c = b := by
    by_contra hne
    push_neg at hne
    have h3 : ({a, b, c} : Finset (E →ₐ[F] ℂ)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair]
      · exact fun e => hne.2 e.symm
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hab, fun e => hne.1 e.symm⟩
    have := Finset.card_le_univ ({a, b, c} : Finset (E →ₐ[F] ℂ))
    omega
  rw [← InfinitePlace.mk_embedding w₁, ← InfinitePlace.mk_embedding w₂, InfinitePlace.mk_eq_iff]
  rcases hcab with e | e
  · left; rw [← ha, ← hc, e]
  · right; rw [← hb, ← hc, e]

end GlobalTheory
