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
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
open IsLocalRing

namespace GlobalTheory

theorem ringKrullDim_le_of_isLocalization' {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] : ringKrullDim S ≤ ringKrullDim R := by
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) ?_
  refine Monotone.strictMono_of_injective ?_ (PrimeSpectrum.localization_comap_injective S M)
  intro p q h
  exact Ideal.comap_mono h

open IsLocalRing in
private theorem ringKrullDim_le_of_isLocalization (A D : Type) [CommRing A] [CommRing D]
    [Algebra A D] (M : Submonoid A) [IsLocalization M D] :
    ringKrullDim D ≤ ringKrullDim A := by
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A D)) ?_
  refine Monotone.strictMono_of_injective (fun p q h => ?_)
    (PrimeSpectrum.localization_comap_injective D M)
  exact Ideal.comap_mono h

open IsLocalRing in
private theorem ringKrullDim_finite_of_finiteType_int (A : Type) [CommRing A]
    [Algebra.FiniteType ℤ A] : ringKrullDim A < ⊤ := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  refine lt_of_le_of_lt (ringKrullDim_le_of_surjective f.toRingHom hf) ?_
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
    IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
  have h : ((1 + Nat.card (Fin n) : ℕ) : WithBot ℕ∞) < ⊤ :=
    WithBot.coe_lt_coe.mpr (ENat.coe_lt_top _)
  exact_mod_cast h

open IsLocalRing in

theorem _root_.GlobalTheory.ringKrullDim_lt_top_of_essFiniteType (D : Type) [CommRing D] [Algebra.EssFiniteType ℤ D] :
    ringKrullDim D < ⊤ :=
  lt_of_le_of_lt
    (ringKrullDim_le_of_isLocalization (Algebra.EssFiniteType.subalgebra ℤ D) D
      (Algebra.EssFiniteType.submonoid ℤ D))
    (ringKrullDim_finite_of_finiteType_int _)

end GlobalTheory
