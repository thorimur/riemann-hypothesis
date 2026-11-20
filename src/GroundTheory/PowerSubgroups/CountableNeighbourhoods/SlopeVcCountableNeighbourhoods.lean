import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
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

namespace GroundTheory.Variant₂.N1

open WeierstrassCurve

def vcX {R : Type*} [CommRing R] (C : WeierstrassCurve.VariableChange R) (x : R) : R :=
  ↑C.u⁻¹ ^ 2 * (x - C.r)

def vcY {R : Type*} [CommRing R] (C : WeierstrassCurve.VariableChange R) (x y : R) : R :=
  ↑C.u⁻¹ ^ 3 * (y - C.s * (x - C.r) - C.t)

theorem slope_variableChange {F : Type*} [Field F] (C : WeierstrassCurve.VariableChange F)
    (W : WeierstrassCurve F) [DecidableEq F] {x₁ x₂ y₁ y₂ : F}
    (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)) :
    (C • W).toAffine.slope (vcX C x₁) (vcX C x₂) (vcY C x₁ y₁) (vcY C x₂ y₂) =
      ↑C.u⁻¹ * (W.toAffine.slope x₁ x₂ y₁ y₂ - C.s) := by
  have hv : (↑C.u⁻¹ : F) ≠ 0 := Units.ne_zero _
  by_cases hx : x₁ = x₂
  · subst hx
    have hy : y₁ ≠ W.toAffine.negY x₁ y₂ := fun h => hxy ⟨rfl, h⟩
    have hyy : y₁ = y₂ := Affine.Y_eq_of_Y_ne h₁ h₂ rfl hy
    subst hyy
    have key : vcY C x₁ y₁ - (C • W).toAffine.negY (vcX C x₁) (vcY C x₁ y₁) =
        (↑C.u⁻¹ : F) ^ 3 * (y₁ - W.toAffine.negY x₁ y₁) := by
      simp only [vcX, vcY, Affine.negY, variableChange_a₁, variableChange_a₃]
      ring
    have hd : y₁ - W.toAffine.negY x₁ y₁ ≠ 0 := sub_ne_zero.mpr hy
    have hd' : vcY C x₁ y₁ - (C • W).toAffine.negY (vcX C x₁) (vcY C x₁ y₁) ≠ 0 := by
      rw [key]; exact mul_ne_zero (pow_ne_zero _ hv) hd
    have hy' : vcY C x₁ y₁ ≠ (C • W).toAffine.negY (vcX C x₁) (vcY C x₁ y₁) :=
      sub_ne_zero.mp hd'
    rw [Affine.slope_of_Y_ne rfl hy, Affine.slope_of_Y_ne rfl hy', key]
    have num : 3 * vcX C x₁ ^ 2 + 2 * (C • W).toAffine.a₂ * vcX C x₁ + (C • W).toAffine.a₄ -
        (C • W).toAffine.a₁ * vcY C x₁ y₁ =
        (↑C.u⁻¹ : F) ^ 4 * ((3 * x₁ ^ 2 + 2 * W.toAffine.a₂ * x₁ + W.toAffine.a₄ -
          W.toAffine.a₁ * y₁) - C.s * (y₁ - W.toAffine.negY x₁ y₁)) := by
      simp only [vcX, vcY, Affine.negY, variableChange_a₁, variableChange_a₂, variableChange_a₄]
      ring
    rw [num]
    set D := y₁ - W.toAffine.negY x₁ y₁
    set N := 3 * x₁ ^ 2 + 2 * W.toAffine.a₂ * x₁ + W.toAffine.a₄ - W.toAffine.a₁ * y₁
    field_simp
  · have hX : vcX C x₁ ≠ vcX C x₂ := by
      intro h
      apply hx
      simp only [vcX] at h
      have := mul_left_cancel₀ (pow_ne_zero 2 hv) h
      exact sub_left_injective this
    rw [Affine.slope_of_X_ne hx, Affine.slope_of_X_ne hX]
    have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    have hXd : vcX C x₁ - vcX C x₂ = (↑C.u⁻¹ : F) ^ 2 * (x₁ - x₂) := by
      simp only [vcX]; ring
    have hYd : vcY C x₁ y₁ - vcY C x₂ y₂ =
        (↑C.u⁻¹ : F) ^ 3 * ((y₁ - y₂) - C.s * (x₁ - x₂)) := by
      simp only [vcY]; ring
    rw [hXd, hYd]
    field_simp

end GroundTheory.Variant₂.N1
