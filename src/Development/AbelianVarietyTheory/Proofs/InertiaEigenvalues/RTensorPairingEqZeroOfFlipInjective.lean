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
open TensorProduct Module

namespace GlobalTheory

theorem rTensor_pairing_eq_zero_of_flip_injective : ∀ (F : Type) [Field F] (B : Type) [AddCommGroup B] [Module F B] (V V' : Type) [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] (m : V →ₗ[F] V' →ₗ[F] F), (∀ y, (∀ x, m x y = 0) → y = 0) → ∀ y : V' ⊗[F] B, (∀ v : V, TensorProduct.lid F B (LinearMap.rTensor B (m v) y) = 0) → y = 0 := by
  intro F _ B _ _ V V' _ _ _ _ _ m hm y hy
  have hinj : Function.Injective m.flip :=
    (injective_iff_map_eq_zero m.flip).2 fun z h =>
      hm z fun x => by simpa using LinearMap.congr_fun h x
  have hsurj : Function.Surjective m := LinearMap.flip_injective_iff₂.1 hinj
  let b := Module.finBasis F V'
  have key : ∀ z : V' ⊗[F] B,
      z = ∑ j, b j ⊗ₜ (TensorProduct.lid F B (LinearMap.rTensor B (b.coord j) z)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v w =>
      simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Basis.coord_apply]
      simp_rw [← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul, b.sum_repr]
    | add z₁ z₂ h₁ h₂ =>
      conv_lhs => rw [h₁, h₂]
      simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
  rw [key y]
  refine Finset.sum_eq_zero fun j _ => ?_
  obtain ⟨v, hv⟩ := hsurj (b.coord j)
  rw [← hv, hy v, TensorProduct.tmul_zero]

end GlobalTheory
