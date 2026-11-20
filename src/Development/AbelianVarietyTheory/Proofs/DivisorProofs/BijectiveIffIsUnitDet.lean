import Mathlib.Algebra.Azumaya.Defs
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
import Mathlib.LinearAlgebra.Basis.MulOpposite
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
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

noncomputable section
open scoped TensorProduct
open Module

namespace GlobalTheory.LocAzumaya

variable {A Λ : Type*} [CommRing A] [Ring Λ] [Algebra A Λ] {ι : Type*} [Fintype ι] [DecidableEq ι]

def structMat (b : Basis ι A Λ) : Matrix (ι × ι) (ι × ι) A :=
  LinearMap.toMatrix (b.tensorProduct b.mulOpposite) b.end (AlgHom.mulLeftRight A Λ).toLinearMap

theorem stdBasis_repr_apply' (M : Matrix ι ι A) (k l : ι) :
    (Matrix.stdBasis A ι ι).repr M (k, l) = M k l := rfl

theorem repr_equiv_apply {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {κ : Type*} (b₁ : Basis κ A M) (b₂ : Basis κ A N) (x : M) :
    b₂.repr (b₁.equiv b₂ (Equiv.refl κ) x) = b₁.repr x := by
  simp [Basis.equiv]

theorem structMat_apply (b : Basis ι A Λ) (k l i j : ι) :
    structMat b (k, l) (i, j) = b.repr (b i * b l * b j) k := by
  rw [structMat, LinearMap.toMatrix_apply]
  simp [Basis.end_repr_apply, Basis.tensorProduct_apply, LinearMap.toMatrix_apply, stdBasis_repr_apply']

theorem bijective_iff_isUnit_det (b : Basis ι A Λ) :
    Function.Bijective (AlgHom.mulLeftRight A Λ) ↔ IsUnit (structMat b).det := by
  set c := b.tensorProduct b.mulOpposite
  set f := (AlgHom.mulLeftRight A Λ).toLinearMap
  haveI := Module.Free.of_basis c
  haveI := Module.Finite.of_basis c
  let e : Module.End A Λ ≃ₗ[A] Λ ⊗[A] Λᵐᵒᵖ := b.end.equiv c (Equiv.refl _)
  have hM : structMat b = LinearMap.toMatrix c c (e.toLinearMap ∘ₗ f) := by
    ext p q
    rw [structMat, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, repr_equiv_apply]
  rw [hM, LinearMap.det_toMatrix, ← LinearMap.isUnit_iff_isUnit_det, Module.End.isUnit_iff]
  constructor
  · intro h; exact e.bijective.comp h
  · intro h
    have := e.symm.bijective.comp h
    simpa [Function.comp_def, f] using this

end GlobalTheory.LocAzumaya
