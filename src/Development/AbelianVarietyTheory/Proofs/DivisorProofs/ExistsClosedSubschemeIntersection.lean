import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem closedSubscheme_inter_exists : ∀ (H Z₁ Z₂ : Scheme.{0}) (i₁ : Z₁ ⟶ H) (i₂ : Z₂ ⟶ H),
    IsClosedImmersion i₁ → IsClosedImmersion i₂ → ∃ (Z₀ : Scheme.{0}) (i₀ : Z₀ ⟶ H),
      IsClosedImmersion i₀ ∧ ∀ (T : Scheme.{0}) (h : T ⟶ H),
        (∃ z, z ≫ i₀ = h) ↔ (∃ z, z ≫ i₁ = h) ∧ ∃ z, z ≫ i₂ = h := by
  intro H Z₁ Z₂ i₁ i₂ h₁ h₂
  refine ⟨pullback i₁ i₂, pullback.snd i₁ i₂ ≫ i₂, inferInstance, ?_⟩
  intro T h
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨⟨z ≫ pullback.fst i₁ i₂, ?_⟩, ⟨z ≫ pullback.snd i₁ i₂, ?_⟩⟩
    · rw [Category.assoc, pullback.condition]
    · rw [Category.assoc]
  · rintro ⟨⟨z₁, hz₁⟩, ⟨z₂, hz₂⟩⟩
    exact ⟨pullback.lift z₁ z₂ (hz₁.trans hz₂.symm), by rw [← Category.assoc, pullback.lift_snd, hz₂]⟩

end GlobalTheory
