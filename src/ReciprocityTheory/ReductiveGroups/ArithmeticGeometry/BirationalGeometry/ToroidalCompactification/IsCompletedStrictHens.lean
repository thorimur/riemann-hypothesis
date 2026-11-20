import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
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

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev Sp (R : Type) [CommRing R] : Scheme.{0} := Spec (CommRingCat.of R)

abbrev spMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') : Sp R' ⟶ Sp R :=
  Spec.map (CommRingCat.ofHom f)

abbrev PSpace (R : Type) [CommRing R] (N : ℕ) : Scheme.{0} :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)

def PSpace.str (R : Type) [CommRing R] (N : ℕ) : PSpace R N ⟶ Sp R :=
  Proj.toSpecZero _ ≫ spMap (algebraMap R ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0))

def IsProjOver {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) : Prop :=
  ∃ (N : ℕ) (i : X ⟶ PSpace R N), IsClosedImmersion i ∧ i ≫ PSpace.str R N = f

def IsQProjOver {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) : Prop :=
  ∃ (N : ℕ) (i : X ⟶ PSpace R N), IsImmersion i ∧ QuasiCompact i ∧ i ≫ PSpace.str R N = f

def IsNormalScheme (X : Scheme.{0}) : Prop :=
  ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)

structure IsCompletedStrictHens (A R : Type) [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R]
    [Algebra A R] [IsLocalHom (algebraMap A R)] : Prop where
  noeth : IsNoetherianRing R
  complete : IsAdicComplete (IsLocalRing.maximalIdeal R) R
  flat : Module.Flat A R
  unram : (IsLocalRing.maximalIdeal A).map (algebraMap A R) = IsLocalRing.maximalIdeal R
  res : IsSepClosure (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField R)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
