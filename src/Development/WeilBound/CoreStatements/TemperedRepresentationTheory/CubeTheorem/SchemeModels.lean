import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.SpreadingModels

def IsModel {R R₀ : Type} [CommRing R] [CommRing R₀] (φ : R₀ →+* R) {Y Y₀ : Scheme.{0}}
    (f : Y ⟶ Spec (CommRingCat.of R)) (f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)) (π : Y ⟶ Y₀) : Prop :=
  Algebra.FiniteType ℤ R₀ ∧ LocallyOfFinitePresentation f₀ ∧ QuasiCompact f₀ ∧ QuasiSeparated f₀ ∧
    IsPullback π f f₀ (Spec.map (CommRingCat.ofHom φ))

def SchemeModels : Prop :=
  ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)),
    LocallyOfFinitePresentation f → QuasiCompact f → QuasiSeparated f →
      ∃ (R₀ : Type) (_ : CommRing R₀) (φ : R₀ →+* R) (Y₀ : Scheme.{0}) (f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀))
        (π : Y ⟶ Y₀), IsModel φ f f₀ π

def Spreads (P : MorphismProperty Scheme.{0}) : Prop :=
  ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (φ : R₀ →+* R) (Y Y₀ : Scheme.{0})
    (f : Y ⟶ Spec (CommRingCat.of R)) (f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)) (π : Y ⟶ Y₀),
    IsModel φ f f₀ π → P f →
      ∃ (R₁ : Type) (_ : CommRing R₁) (ψ : R₀ →+* R₁) (φ₁ : R₁ →+* R), φ₁.comp ψ = φ ∧
        Algebra.FiniteType ℤ R₁ ∧ P (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ)))

end GlobalTheory.SpreadingModels
