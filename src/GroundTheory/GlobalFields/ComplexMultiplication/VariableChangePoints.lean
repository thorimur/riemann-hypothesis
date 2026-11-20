import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
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
import Std.Tactic.BVDecide.Normalize.Prop

namespace GroundTheory.Global

open WeierstrassCurve

variable {F : Type*} [Field F]

section VariableChangePoint

theorem nonsingular_variableChange (C : VariableChange F) (W : WeierstrassCurve F) {x y : F}
    (h : W.toAffine.Nonsingular x y) :
    (C • W).toAffine.Nonsingular (↑C.u⁻¹ ^ 2 * (x - C.r))
      (↑C.u⁻¹ ^ 3 * (y - C.s * (x - C.r) - C.t)) := by
  rw [Affine.nonsingular_iff'] at h ⊢
  obtain ⟨he, hd⟩ := h
  rw [Affine.equation_iff'] at he ⊢
  have hv : (↑C.u⁻¹ : F) ≠ 0 := Units.ne_zero _
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆]
  set v : F := ↑C.u⁻¹
  refine ⟨?_, ?_⟩
  · linear_combination v ^ 6 * he
  · by_contra hc
    push Not at hc
    obtain ⟨h1, h2⟩ := hc
    have hY : 2 * y + W.a₁ * x + W.a₃ = 0 := by
      have : v ^ 3 * (2 * y + W.a₁ * x + W.a₃) = 0 := by linear_combination h2
      simpa [hv] using this
    have hX : W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 0 := by
      have : v ^ 4 * (W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)) = 0 := by
        linear_combination h1 - v ^ 4 * C.s * hY
      simpa [hv] using this
    rcases hd with hd | hd
    · exact hd hX
    · exact hd hY

def variableChangePoint (C : VariableChange F) {W W' : WeierstrassCurve F} (hC : C • W = W') :
    W.toAffine.Point → W'.toAffine.Point
  | .zero => .zero
  | .some x y h => .some (↑C.u⁻¹ ^ 2 * (x - C.r)) (↑C.u⁻¹ ^ 3 * (y - C.s * (x - C.r) - C.t))
      (by subst hC; exact nonsingular_variableChange C W h)

@[simp]
theorem variableChangePoint_zero (C : VariableChange F) {W W' : WeierstrassCurve F}
    (hC : C • W = W') : variableChangePoint C hC .zero = .zero := rfl

theorem variableChangePoint_some (C : VariableChange F) {W W' : WeierstrassCurve F}
    (hC : C • W = W') {x y : F} (h : W.toAffine.Nonsingular x y) :
    variableChangePoint C hC (.some x y h) =
      .some (↑C.u⁻¹ ^ 2 * (x - C.r)) (↑C.u⁻¹ ^ 3 * (y - C.s * (x - C.r) - C.t))
        (by subst hC; exact nonsingular_variableChange C W h) := rfl

end VariableChangePoint

end GroundTheory.Global
