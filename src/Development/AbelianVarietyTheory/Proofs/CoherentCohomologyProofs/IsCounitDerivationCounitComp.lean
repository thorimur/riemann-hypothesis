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
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open TensorProduct

namespace GlobalTheory.LeftRightDerivations

variable {k : Type*} {H : Type*} [CommSemiring k] [CommSemiring H] [Bialgebra k H]

def IsCounitDerivation (φ : H →ₗ[k] k) : Prop :=
  ∀ a b : H, φ (a * b) =
    Coalgebra.counit (R := k) a * φ b + Coalgebra.counit (R := k) b * φ a

theorem isCounitDerivation_iff (φ : H →ₗ[k] k) :
    IsCounitDerivation φ ↔ ∀ a b : H, φ (a * b) =
      Coalgebra.counit (R := k) a * φ b + Coalgebra.counit (R := k) b * φ a := Iff.rfl

noncomputable def contrRight (φ : H →ₗ[k] k) : H ⊗[k] H →ₗ[k] H :=
  (TensorProduct.rid k H).toLinearMap ∘ₗ LinearMap.lTensor H φ

noncomputable def contrLeft (φ : H →ₗ[k] k) : H ⊗[k] H →ₗ[k] H :=
  (TensorProduct.lid k H).toLinearMap ∘ₗ LinearMap.rTensor H φ

@[simp] theorem contrRight_tmul (φ : H →ₗ[k] k) (a b : H) :
    contrRight φ (a ⊗ₜ[k] b) = φ b • a := by
  simp [contrRight]

@[simp] theorem contrLeft_tmul (φ : H →ₗ[k] k) (a b : H) :
    contrLeft φ (a ⊗ₜ[k] b) = φ a • b := by
  simp [contrLeft]

theorem contrRight_counit_comul (a : H) :
    contrRight (Coalgebra.counit (R := k)) (Coalgebra.comul (R := k) a) = a := by

  simp [contrRight, Coalgebra.lTensor_counit_comul]

theorem contrLeft_counit_comul (a : H) :
    contrLeft (Coalgebra.counit (R := k)) (Coalgebra.comul (R := k) a) = a := by
  simp [contrLeft, Coalgebra.rTensor_counit_comul]

theorem contrRight_mul {φ : H →ₗ[k] k} (hφ : IsCounitDerivation φ) (s t : H ⊗[k] H) :
    contrRight φ (s * t) =
      contrRight (Coalgebra.counit (R := k)) s * contrRight φ t +
        contrRight (Coalgebra.counit (R := k)) t * contrRight φ s := by

  induction s using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [add_mul, map_add, hx, hy]; ring
  | tmul a b =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [mul_add, map_add, hx, hy]; ring
    | tmul c d =>
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      simp only [contrRight_tmul, hφ b d, Algebra.smul_def, map_add, map_mul]
      ring

theorem contrLeft_mul {φ : H →ₗ[k] k} (hφ : IsCounitDerivation φ) (s t : H ⊗[k] H) :
    contrLeft φ (s * t) =
      contrLeft (Coalgebra.counit (R := k)) s * contrLeft φ t +
        contrLeft (Coalgebra.counit (R := k)) t * contrLeft φ s := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [add_mul, map_add, hx, hy]; ring
  | tmul a b =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [mul_add, map_add, hx, hy]; ring
    | tmul c d =>
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      simp only [contrLeft_tmul, hφ a c, Algebra.smul_def, map_add, map_mul]
      ring

theorem contrRight_one (φ : H →ₗ[k] k) : contrRight φ 1 = φ 1 • (1 : H) := by
  rw [Algebra.TensorProduct.one_def, contrRight_tmul]

theorem contrLeft_one (φ : H →ₗ[k] k) : contrLeft φ 1 = φ 1 • (1 : H) := by
  rw [Algebra.TensorProduct.one_def, contrLeft_tmul]

theorem counit_contrRight (φ : H →ₗ[k] k) (s : H ⊗[k] H) :
    Coalgebra.counit (R := k) (contrRight φ s) =
      φ (contrLeft (Coalgebra.counit (R := k)) s) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem counit_contrLeft (φ : H →ₗ[k] k) (s : H ⊗[k] H) :
    Coalgebra.counit (R := k) (contrLeft φ s) =
      φ (contrRight (Coalgebra.counit (R := k)) s) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

section Ring

variable {k : Type*} {H : Type*} [CommRing k] [CommRing H] [Bialgebra k H]

theorem IsCounitDerivation.map_one {φ : H →ₗ[k] k} (hφ : IsCounitDerivation φ) : φ 1 = 0 := by

  have h := hφ 1 1
  rw [mul_one, Bialgebra.counit_one, one_mul] at h
  simpa using h

noncomputable def derivRight (φ : H →ₗ[k] k) (hφ : IsCounitDerivation φ) : Derivation k H H where
  toLinearMap := contrRight φ ∘ₗ Coalgebra.comul (R := k)
  map_one_eq_zero' := by
    rw [LinearMap.comp_apply, Bialgebra.comul_one, contrRight_one, hφ.map_one, zero_smul]
  leibniz' a b := by
    simp only [LinearMap.comp_apply, Bialgebra.comul_mul, contrRight_mul hφ,
      contrRight_counit_comul, smul_eq_mul]

noncomputable def derivLeft (φ : H →ₗ[k] k) (hφ : IsCounitDerivation φ) : Derivation k H H where
  toLinearMap := contrLeft φ ∘ₗ Coalgebra.comul (R := k)
  map_one_eq_zero' := by
    rw [LinearMap.comp_apply, Bialgebra.comul_one, contrLeft_one, hφ.map_one, zero_smul]
  leibniz' a b := by
    simp only [LinearMap.comp_apply, Bialgebra.comul_mul, contrLeft_mul hφ,
      contrLeft_counit_comul, smul_eq_mul]

theorem derivRight_apply (φ : H →ₗ[k] k) (hφ : IsCounitDerivation φ) (y : H) :
    derivRight φ hφ y =
      TensorProduct.rid k H (LinearMap.lTensor H φ (Coalgebra.comul (R := k) y)) := rfl

theorem derivLeft_apply (φ : H →ₗ[k] k) (hφ : IsCounitDerivation φ) (y : H) :
    derivLeft φ hφ y =
      TensorProduct.lid k H (LinearMap.rTensor H φ (Coalgebra.comul (R := k) y)) := rfl

theorem counit_derivRight (φ : H →ₗ[k] k) (hφ : IsCounitDerivation φ) (y : H) :
    Coalgebra.counit (R := k) (derivRight φ hφ y) = φ y := by
  have h : derivRight φ hφ y = contrRight φ (Coalgebra.comul (R := k) y) := rfl
  rw [h, counit_contrRight, contrLeft_counit_comul]

theorem counit_derivLeft (φ : H →ₗ[k] k) (hφ : IsCounitDerivation φ) (y : H) :
    Coalgebra.counit (R := k) (derivLeft φ hφ y) = φ y := by
  have h : derivLeft φ hφ y = contrLeft φ (Coalgebra.comul (R := k) y) := rfl
  rw [h, counit_contrLeft, contrRight_counit_comul]

theorem isCounitDerivation_counit_comp (D : Derivation k H H) :
    IsCounitDerivation (Coalgebra.counit (R := k) ∘ₗ D.toLinearMap) := by

  intro a b
  simp [Derivation.leibniz, Bialgebra.counit_mul]

end Ring

end GlobalTheory.LeftRightDerivations
