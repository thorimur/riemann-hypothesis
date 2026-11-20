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
import Mathlib.Topology.Sheaves.Init
open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem reduced_quot_tensor_of_reduced_modp :
    ∀ (O : Type) [CommRing O] (k : Type) [Field k] (p : ℕ) (ϖ : O), (p : k) = 0 →
      IsReduced (k ⊗[ℤ] (O ⧸ Ideal.span {(p : O), ϖ})) →
      IsReduced ((k ⊗[ℤ] O) ⧸ Ideal.span {(1 : k) ⊗ₜ[ℤ] ϖ}) := by
  intro O _ k _ p ϖ hp hred
  set I : Ideal O := Ideal.span {(p : O), ϖ}
  set f := Algebra.TensorProduct.map (AlgHom.id ℤ k) (Ideal.Quotient.mkₐ ℤ I) with hf
  have hker : RingHom.ker f.toRingHom = Ideal.span {(1 : k) ⊗ₜ[ℤ] ϖ} := by
    have h := Algebra.TensorProduct.lTensor_ker (A := k) (Ideal.Quotient.mkₐ ℤ I)
      (Ideal.Quotient.mkₐ_surjective ℤ I)
    have hk : RingHom.ker (Ideal.Quotient.mkₐ ℤ I) = I := Ideal.Quotient.mkₐ_ker ℤ I
    have h0 : (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] k ⊗[ℤ] O) (p : O) = 0 := by
      rw [map_natCast]
      have : ((p : ℕ) : k ⊗[ℤ] O) = (Algebra.TensorProduct.includeLeft : k →ₐ[ℤ] k ⊗[ℤ] O) (p : k) := by
        rw [map_natCast]
      rw [this, hp, map_zero]
    have h1 : (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] k ⊗[ℤ] O) ϖ = (1 : k) ⊗ₜ[ℤ] ϖ := rfl
    have e := h
    rw [hk] at e
    change RingHom.ker f.toRingHom = _ at e
    rw [e, Ideal.map_span, Set.image_pair]
    erw [h0, h1]
    exact Ideal.span_insert_zero
  have hinj : Function.Injective (RingHom.kerLift f.toRingHom) := RingHom.kerLift_injective _
  have hR : IsReduced (k ⊗[ℤ] O ⧸ RingHom.ker f.toRingHom) := isReduced_of_injective _ hinj
  rw [hker] at hR
  exact hR

end GlobalTheory
