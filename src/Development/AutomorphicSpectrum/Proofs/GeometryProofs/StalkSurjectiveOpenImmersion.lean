import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
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
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem stalkMap_comp_surjective_of_open_part :
    ∀ (S X₀ Xg X' : Scheme.{0}) (e : Xg ⟶ X₀) (f : X' ⟶ Xg) (W' : X'.Opens)
      (jW : W'.toScheme ⟶ S) (jQ : S ⟶ Xg), IsPreimmersion e → IsOpenImmersion jQ → IsIso jW →
      jW ≫ jQ = W'.ι ≫ f → ∀ x ∈ W', Function.Surjective ((f ≫ e).stalkMap x).hom := by
  intro S X₀ Xg X' e f W' jW jQ he hjQ hjW hcomm x hx
  have := he
  have hO : IsOpenImmersion (W'.ι ≫ f) := by
    rw [← hcomm]
    infer_instance
  obtain ⟨y, rfl⟩ : ∃ y : W'.toScheme, W'.ι y = x := ⟨⟨x, hx⟩, rfl⟩
  have h1 : Function.Surjective ((W'.ι ≫ f).stalkMap y) :=
    Scheme.Hom.stalkMap_surjective (W'.ι ≫ f) y
  have := (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion W'.ι)).2 y
  have hι : Function.Bijective (W'.ι.stalkMap y) := ConcreteCategory.bijective_of_isIso _
  have key : Function.Surjective (f.stalkMap (W'.ι y)) := by
    intro t
    obtain ⟨s, hs⟩ := h1 (W'.ι.stalkMap y t)
    refine ⟨s, hι.1 ?_⟩
    rw [Scheme.Hom.stalkMap_comp] at hs
    exact hs
  rw [Scheme.Hom.stalkMap_comp]
  exact key.comp (Scheme.Hom.stalkMap_surjective e (f (W'.ι y)))

end GlobalTheory.CompanionTheory.Ar.Flat
