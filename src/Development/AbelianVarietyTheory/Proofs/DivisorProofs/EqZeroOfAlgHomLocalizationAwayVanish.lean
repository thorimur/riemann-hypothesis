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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
set_option autoImplicit false

namespace GlobalTheory

theorem points_separate_localization_away (R K C : Type) [CommRing R] [Field K] [Algebra R K]
    [CommRing C] [Algebra R C] (h : ∀ a : C, (∀ ψ : C →ₐ[R] K, ψ a = 0) → a = 0)
    (e : C) (y : Localization.Away e)
    (hy : ∀ χ : Localization.Away e →ₐ[R] K, χ y = 0) : y = 0 := by
  obtain ⟨n, x, hx⟩ := IsLocalization.Away.surj e y
  have hxe : x * e = 0 := by
    apply h
    intro ψ
    rw [map_mul]
    by_cases he : ψ e = 0
    · rw [he, mul_zero]
    · have hu : IsUnit ((ψ : C →+* K) e) := Ne.isUnit he
      let f : Localization.Away e →+* K := IsLocalization.Away.lift e hu
      have hf : ∀ c : C, f (algebraMap C (Localization.Away e) c) = ψ c := fun c =>
        IsLocalization.Away.lift_eq e hu c
      let χ : Localization.Away e →ₐ[R] K :=
        { f with
          commutes' := fun r => by
            change f (algebraMap R (Localization.Away e) r) = _
            rw [IsScalarTower.algebraMap_apply R C (Localization.Away e), hf, AlgHom.commutes] }
      have h0 : f y = 0 := hy χ
      have : ψ x = 0 := by
        rw [← hf x, ← hx, map_mul, h0, zero_mul]
      rw [this, zero_mul]
  have hue : IsUnit (algebraMap C (Localization.Away e) e) :=
    IsLocalization.Away.algebraMap_isUnit e
  have h1 : y * algebraMap C (Localization.Away e) e ^ (n + 1) = 0 := by
    rw [pow_succ, ← mul_assoc, hx, ← map_mul, hxe, map_zero]
  exact (hue.pow (n + 1)).mul_left_eq_zero.mp h1

end GlobalTheory
