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
import Mathlib.RingTheory.Radical.NatInt
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
open NumberField GlobalTheory.Shintani MeasureTheory Filter Topology

namespace GlobalTheory.Shintani

theorem denseRange_realEmbeddings :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F],
      DenseRange (fun (x : F) (σ : F →+* ℝ) => σ x) := by
  intro F _ _ _
  have h1 := NumberField.InfiniteAdeleRing.denseRange_algebraMap F
  let E : ∀ w : InfinitePlace F, w.Completion → ℝ := fun w z =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) z
  have hs : Function.Surjective (Pi.map E) := by
    intro y
    refine ⟨fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm (y w), ?_⟩
    funext w
    exact (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).apply_symm_apply (y w)
  have hc : Continuous (Pi.map E) := by
    refine continuous_pi fun w => ?_
    have : (E w) = InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal w) := by
      funext z; exact InfinitePlace.Completion.ringEquivRealOfIsReal_apply _ z
    change Continuous fun a : (∀ v : InfinitePlace F, v.Completion) => E w (a w)
    rw [this]
    exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
      (IsTotallyReal.isReal w)).continuous.comp (continuous_apply w)
  have h2 := hs.denseRange.comp h1 hc
  let g : (F →+* ℝ) → InfinitePlace F := fun σ => InfinitePlace.mk (Complex.ofRealHom.comp σ)
  have hreal : ∀ σ : F →+* ℝ, ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
    intro σ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp [ComplexEmbedding.conjugate_coe_eq]
  have hemb : ∀ σ : F →+* ℝ, (g σ).embedding = Complex.ofRealHom.comp σ := fun σ =>
    InfinitePlace.embedding_mk_eq_of_isReal (hreal σ)
  have hg : Function.Injective g := by
    intro σ τ h
    have := hemb σ
    rw [h, hemb τ] at this
    ext x
    have h3 := congrArg (fun f : F →+* ℂ => f x) this
    simp only [RingHom.comp_apply, Complex.ofRealHom_eq_coe, Complex.ofReal_inj] at h3
    exact h3.symm
  have hval : ∀ (x : F) (σ : F →+* ℝ), Pi.map E (algebraMap F (InfiniteAdeleRing F) x) (g σ) = σ x := by
    intro x σ
    change E (g σ) (algebraMap F (InfiniteAdeleRing F) x (g σ)) = σ x
    rw [InfiniteAdeleRing.algebraMap_apply]
    have e1 := InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe (IsTotallyReal.isReal (g σ))
      ((WithAbs.equiv (g σ).1).symm x)
    have e2 := InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal (g σ)) x
    apply Complex.ofReal_injective
    simp only [E, InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
    have e3 : ((InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal (g σ)))
        { toCompletion := ↑(WithAbs.toAbs (g σ).1 x) } : ℂ) = (g σ).embedding x := by
      rw [← e2]
      simp only [RingEquiv.apply_symm_apply, WithAbs.equiv_symm_apply, WithAbs.equiv_apply] at e1
      exact congrArg _ e1
    rw [e3, hemb σ]
    rfl

  let P : (InfinitePlace F → ℝ) → ((F →+* ℝ) → ℝ) := fun y σ => y (g σ)
  have hPs : Function.Surjective P := fun z => ⟨Function.extend g z 0, funext fun σ => hg.extend_apply z 0 σ⟩
  have hPc : Continuous P := continuous_pi fun σ => continuous_apply (g σ)
  convert hPs.denseRange.comp h2 hPc using 1
  funext x σ
  exact (hval x σ).symm

end GlobalTheory.Shintani
