import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
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
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.ChartGeoPf

def ChartStdGeo : Prop := ∀ {X S : Scheme.{0}} (p : X ⟶ S) (n : ℕ) [SmoothOfRelativeDimension n p] (x : X)
  (W : X.Opens), x ∈ W → ∃ (U : S.Opens) (_ : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V)
    (hUV : V ≤ p ⁻¹ᵁ U), x ∈ V ∧ V ≤ W ∧ (p.appLE U V hUV).hom.IsStandardSmoothOfRelativeDimension n

def RangeKer : Prop := ∀ {X Z : Scheme.{0}} (ι : Z ⟶ X) [IsClosedImmersion ι] (V : X.Opens) (hV : IsAffineOpen V)
  (y : Spec Γ(X, V)), hV.fromSpec y ∈ Set.range ι ↔ RingHom.ker (ι.app V).hom ≤ (show PrimeSpectrum Γ(X, V) from y).asIdeal

def QuotLoc : Prop := ∀ (n : ℕ) (A B T : Type) [CommRing A] [CommRing B] [CommRing T] [Algebra A B] (π : B →+* T),
  Function.Surjective π → RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (π.comp (algebraMap A B)) →
  ∀ P : Ideal B, P.IsPrime → RingHom.ker π ≤ P → ∃ g ∉ P,
    Algebra.IsStandardSmoothOfRelativeDimension n A (Localization.Away g ⧸ (RingHom.ker π).map (algebraMap B (Localization.Away g)))

end LateralTheory.E.ChartGeoPf
