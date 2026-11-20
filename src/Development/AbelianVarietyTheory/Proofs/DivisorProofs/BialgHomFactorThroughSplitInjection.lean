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
import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

namespace GlobalTheory

theorem bialgHom_factor_through_split :
    ∀ (O : Type) [CommRing O] (A B D : Type) [CommRing A] [CommRing B] [CommRing D] [Bialgebra O A] [Bialgebra O B] [Bialgebra O D] (j : B →ₐc[O] A) (ρ : A →ₗ[O] B) (f : D →ₐc[O] A), (∀ b, ρ (j b) = b) → (∀ d, f d ∈ Set.range j) → ∃ g : D →ₐc[O] B, ∀ d, j (g d) = f d := by
  intro O _ A B D _ _ _ _ _ _ j ρ f hρ hf
  have hjinj : Function.Injective j := fun x y h => by
    have := congrArg ρ h; rwa [hρ, hρ] at this
  have hjg : ∀ d, j (ρ (f d)) = f d := fun d => by
    obtain ⟨b, hb⟩ := hf d; rw [← hb, hρ]
  have hmapinj : Function.Injective (TensorProduct.map (j : B →ₗ[O] A) (j : B →ₗ[O] A)) := by
    have hid : (TensorProduct.map ρ ρ).comp (TensorProduct.map (j : B →ₗ[O] A) (j : B →ₗ[O] A)) = LinearMap.id := by
      apply TensorProduct.ext'
      intro x y
      simp [hρ]
    intro x y h
    have := congrArg (TensorProduct.map ρ ρ) h
    simpa [← LinearMap.comp_apply, hid] using this
  let gl : D →ₗ[O] B := ρ ∘ₗ (f : D →ₗ[O] A)
  have hgl : ∀ d, j (gl d) = f d := hjg
  have hcomp : (j : B →ₗ[O] A) ∘ₗ gl = (f : D →ₗ[O] A) := LinearMap.ext hgl
  refine ⟨{ gl with
    counit_comp := ?_
    map_comp_comul := ?_
    map_one' := ?_
    map_mul' := ?_ }, hgl⟩
  · ext d
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [← CoalgHomClass.counit_comp_apply j, hgl, CoalgHomClass.counit_comp_apply]
  · ext d
    apply hmapinj
    show TensorProduct.map (j : B →ₗ[O] A) (j : B →ₗ[O] A) (TensorProduct.map gl gl (comul d)) =
      TensorProduct.map (j : B →ₗ[O] A) (j : B →ₗ[O] A) (comul (gl d))
    rw [CoalgHomClass.map_comp_comul_apply j, hgl, ← LinearMap.comp_apply, ← TensorProduct.map_comp, hcomp,
      CoalgHomClass.map_comp_comul_apply f]
  · apply hjinj
    show j (gl 1) = j 1
    rw [hgl, map_one, map_one]
  · intro x y
    apply hjinj
    show j (gl (x * y)) = j (gl x * gl y)
    rw [hgl, map_mul, map_mul, hgl, hgl]

end GlobalTheory
