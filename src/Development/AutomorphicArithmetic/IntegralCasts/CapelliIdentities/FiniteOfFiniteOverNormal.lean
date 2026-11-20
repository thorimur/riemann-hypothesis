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
import Mathlib.RingTheory.NoetherNormalization
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

namespace UpperTheory

open nonZeroDivisors

private theorem finite_of_finite_over_normal (P A K : Type*) [CommRing P] [IsDomain P]
    [CharZero P] [IsIntegrallyClosed P] [IsNoetherianRing P] [CommRing A] [IsDomain A]
    [Algebra P A] [FaithfulSMul P A] [Module.Finite P A] [Field K] [Algebra A K]
    [IsFractionRing A K] : Module.Finite A (integralClosure A K) := by
  letI : Algebra P K := ((algebraMap A K).comp (algebraMap P A)).toAlgebra
  haveI : IsScalarTower P A K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FaithfulSMul P K := (faithfulSMul_iff_algebraMap_injective P K).mpr
    ((IsFractionRing.injective A K).comp (FaithfulSMul.algebraMap_injective P A))
  letI : Algebra (FractionRing P) K := FractionRing.liftAlgebra P K
  haveI : IsScalarTower P (FractionRing P) K := FractionRing.isScalarTower_liftAlgebra P K
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A P⁰) K := inferInstance
  haveI : FiniteDimensional (FractionRing P) K := Module.Finite.of_isLocalization P A P⁰
  haveI : CharZero (FractionRing P) := IsFractionRing.charZero P
  haveI : Algebra.IsSeparable (FractionRing P) K := inferInstance
  haveI : IsIntegralClosure (integralClosure A K) P K :=
    ⟨Subtype.val_injective, fun {x} =>
      ⟨fun hx => ⟨⟨x, hx.tower_top⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ isIntegral_trans _ y.2⟩⟩
  haveI : Module.Finite P (integralClosure A K) :=
    IsIntegralClosure.finite P (FractionRing P) K (integralClosure A K)
  exact Module.Finite.of_restrictScalars_finite P A (integralClosure A K)

theorem integralClosure_finite (k A K : Type*) [Field k] [CharZero k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [Field K] [Algebra A K] [IsFractionRing A K] :
    Module.Finite A (integralClosure A K) := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  letI : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin s) k) A := hfin
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  exact finite_of_finite_over_normal (MvPolynomial (Fin s) k) A K

end UpperTheory
