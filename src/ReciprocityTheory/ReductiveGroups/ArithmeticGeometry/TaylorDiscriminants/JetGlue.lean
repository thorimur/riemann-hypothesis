import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Scheme
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

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ReciprocityTheory.ChartRestriction.G.TB

abbrev JetRing (S : Type) [CommRing S] (κ : Type) (m : ℕ) : Type :=
  MvPolynomial κ S ⧸ (Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ S))) ^ (m + 1)

abbrev JetLoc (S : Type) [CommRing S] (κ : Type) (m : ℕ) (𝔭 : Ideal S) [𝔭.IsPrime] : Type :=
  Localization (Algebra.algebraMapSubmonoid (JetRing S κ m) 𝔭.primeCompl)

def JetGlueSt : Prop :=
  ∀ (S : Type) [CommRing S] (κ : Type) [Finite κ] (m : ℕ) (X : Scheme.{0})
    (f g : Spec (CommRingCat.of (JetRing S κ m)) ⟶ X),
    (∀ (𝔭 : Ideal S) [𝔭.IsPrime],
      Spec.map (CommRingCat.ofHom (algebraMap (JetRing S κ m) (JetLoc S κ m 𝔭))) ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap (JetRing S κ m) (JetLoc S κ m 𝔭))) ≫ g) →
    f = g

end ReciprocityTheory.ChartRestriction.G.TB
