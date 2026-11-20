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
import Mathlib.NumberTheory.ClassNumber.AdmissibleAbs
import Mathlib.NumberTheory.ClassNumber.Finite
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

namespace GlobalTheory.IntClosedOrder

theorem numberField_fractionRing (A : Type) [CommRing A] [IsDomain A] [CharZero A]
    [Module.Finite ℤ A] : NumberField (FractionRing A) := by
  haveI : @IsScalarTower ℤ ℚ (FractionRing A) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [eq_intCast (algebraMap ℤ ℚ), map_intCast, eq_intCast])
  haveI : FiniteDimensional ℚ (FractionRing A) :=
    Module.Finite.of_isLocalization ℤ A (nonZeroDivisors ℤ)
  exact {}

theorem isIntegralClosure_int (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Module.Finite ℤ A] : IsIntegralClosure A ℤ (FractionRing A) := by
  haveI : Algebra.IsIntegral ℤ A := Algebra.IsIntegral.of_finite ℤ A
  refine ⟨IsFractionRing.injective A (FractionRing A), fun {x} => ⟨fun hx => ?_, ?_⟩⟩
  · exact (IsIntegrallyClosed.isIntegral_iff (R := A) (K := FractionRing A)).mp
      (IsIntegral.tower_top (A := A) hx)
  · rintro ⟨a, rfl⟩
    exact (Algebra.IsIntegral.isIntegral (R := ℤ) a).algebraMap

theorem isDedekindDomain_and_finite_classGroup : ∀ (A : Type) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [CharZero A] [Module.Finite ℤ A],
    IsDedekindDomain A ∧ Finite (ClassGroup A) := by
  intro A _ _ _ _ _
  haveI := numberField_fractionRing A
  haveI := isIntegralClosure_int A
  haveI : @IsScalarTower ℤ ℚ (FractionRing A) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [eq_intCast (algebraMap ℤ ℚ), map_intCast, eq_intCast])
  refine ⟨IsIntegralClosure.isDedekindDomain ℤ ℚ (FractionRing A) A, ?_⟩
  letI := ClassGroup.fintypeOfAdmissibleOfFinite ℚ (FractionRing A) AbsoluteValue.absIsAdmissible
    (S := A)
  exact Finite.of_fintype _

end GlobalTheory.IntClosedOrder
