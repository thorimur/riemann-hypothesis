import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
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

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.KeyFin

theorem finite_preimage_of_isPullback_of_finite_base :
    ∀ (X X' S S' : Scheme.{0}) (h : X ⟶ S) (h' : X' ⟶ S') (φ : X' ⟶ X) (f : S' ⟶ S) (Z : Set X),
      LocallyOfFiniteType h → QuasiCompact h → IsPullback φ h' h f → Finite S' → IsClosed Z →
      Z.Finite → (φ ⁻¹' Z).Finite := by
  intro X X' S S' h h' φ f Z _ _ H _ hZ hfin
  let I := Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨Z, hZ⟩
  have hr : Set.range I.subschemeι = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
  have hf : Finite I.subscheme := by
    have : Finite (Set.range I.subschemeι) := by rw [hr]; exact hfin.to_subtype
    exact Finite.of_injective_finite_range I.subschemeι.isClosedEmbedding.injective
  have hq : LocallyQuasiFinite (I.subschemeι ≫ h) :=
    .of_finite_preimage_singleton _ fun _ => Set.toFinite _
  have P := (IsPullback.of_hasPullback I.subschemeι φ).paste_vert H
  have h1 : LocallyQuasiFinite (pullback.snd I.subschemeι φ ≫ h') :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) P hq
  have h2 : QuasiCompact (pullback.snd I.subschemeι φ ≫ h') :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) P inferInstance
  have h3 : (Set.univ : Set ↑(pullback I.subschemeι φ)).Finite := by
    have := (Set.toFinite (Set.univ : Set S')).preimage'
      (f := (pullback.snd I.subschemeι φ ≫ h')) fun _ _ =>
        (pullback.snd I.subschemeι φ ≫ h').finite_preimage_singleton _
    simpa using this
  rw [← hr, ← Scheme.Pullback.range_snd, ← Set.image_univ]
  exact h3.image _

end GlobalTheory.KeyFin
