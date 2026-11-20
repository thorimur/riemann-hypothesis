import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.locallyFinite_of_algMod_criterion :
    ∀ (X Y : Type) [MeasurableSpace X] (μ : Measure X) (V : Submodule ℂ (Y → ℂ)), FiniteDimensional ℂ V → ∀ F : X → Y → ℂ, (∀ x, F x ∈ V) → (∀ y, Integrable (fun x => F x y) μ) → (fun y => ∫ x, F x y ∂μ) ∈ V := by
  intro X Y _ μ V hV F hF hI
  classical
  let ev : Y → (V →ₗ[ℂ] ℂ) := fun y => (LinearMap.proj y).comp V.subtype
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro z hz
    by_contra h
    apply hz
    ext y
    by_contra hy
    exact h ⟨ev y, ⟨y, rfl⟩, hy⟩
  have hint : ∀ φ : V →ₗ[ℂ] ℂ, Integrable (fun x => φ ⟨F x, hF x⟩) μ := by
    intro φ
    have hφ : φ ∈ Submodule.span ℂ (Set.range ev) := hspan ▸ Submodule.mem_top
    induction hφ using Submodule.span_induction with
    | mem f hf => obtain ⟨y, rfl⟩ := hf; exact hI y
    | zero => simp
    | add f g _ _ hf hg => exact hf.add hg
    | smul c f _ hf => exact hf.const_mul c
  let b := Module.finBasis ℂ V
  have key : (fun y => ∫ x, F x y ∂μ)
      = ∑ i, (∫ x, b.coord i ⟨F x, hF x⟩ ∂μ) • ((b i : V) : Y → ℂ) := by
    funext y
    have h1 : ∀ x, F x y = ∑ i, b.coord i ⟨F x, hF x⟩ * ((b i : V) : Y → ℂ) y := by
      intro x
      have h := congrArg (ev y) (b.sum_repr ⟨F x, hF x⟩)
      rw [map_sum] at h
      simp only [map_smul] at h
      exact h.symm
    simp only [h1, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_finset_sum _ (fun i _ => (hint (b.coord i)).mul_const _)]
    exact Finset.sum_congr rfl fun i _ => integral_mul_const _ _
  rw [key]
  exact V.sum_mem fun i _ => V.smul_mem _ (b i).2
