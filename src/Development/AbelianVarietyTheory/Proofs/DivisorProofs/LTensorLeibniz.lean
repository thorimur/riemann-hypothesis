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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory.TensorLeibnizRule

open TensorProduct

theorem lTensor_leibniz {R S : Type} [CommRing R] [Algebra ℂ R] [CommRing S] [Algebra ℂ S]
    (d : Derivation ℂ S S) (x y : TensorProduct ℂ R S) :
    (LinearMap.lTensor R (↑d : S →ₗ[ℂ] S) : TensorProduct ℂ R S → TensorProduct ℂ R S) (x * y) =
      x * (LinearMap.lTensor R (↑d : S →ₗ[ℂ] S) : TensorProduct ℂ R S → TensorProduct ℂ R S) y +
      y * (LinearMap.lTensor R (↑d : S →ₗ[ℂ] S) : TensorProduct ℂ R S → TensorProduct ℂ R S) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r s =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r' s' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.lTensor_tmul, Derivation.coeFn_coe,
        Derivation.leibniz, smul_eq_mul, TensorProduct.tmul_add]
      rw [mul_comm r' r]
    | add y₁ y₂ h₁ h₂ =>
      rw [mul_add, map_add, h₁, h₂, map_add, mul_add, add_mul]
      abel
  | add x₁ x₂ h₁ h₂ =>
    rw [add_mul, map_add, h₁, h₂, map_add, add_mul, mul_add]
    abel

end GlobalTheory.TensorLeibnizRule
