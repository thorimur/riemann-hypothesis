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

noncomputable section

namespace GlobalTheory.AffineCurveNbhd

def IsNbhd (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) : Prop :=
  (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) ∧
  (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f})

theorem awayHom_isUnit {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A'] [Algebra A A'']
    (φ : A' →ₐ[A] A'') (f : A) :
    IsUnit (((algebraMap A'' (Localization.Away (algebraMap A A'' f))).comp φ.toRingHom) (algebraMap A A' f)) := by
  rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
  exact IsLocalization.Away.algebraMap_isUnit _

def awayHom {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A'] [Algebra A A'']
    (φ : A' →ₐ[A] A'') (f : A) : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A'' f) :=
  Localization.awayLift ((algebraMap A'' _).comp φ.toRingHom) _ (awayHom_isUnit φ f)

theorem awayHom_comp_algebraMap {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A']
    [Algebra A A''] (φ : A' →ₐ[A] A'') (f : A) :
    (awayHom φ f).comp (algebraMap A' _) = (algebraMap A'' _).comp φ.toRingHom :=
  IsLocalization.Away.lift_comp _ (awayHom_isUnit φ f)

end GlobalTheory.AffineCurveNbhd

end
