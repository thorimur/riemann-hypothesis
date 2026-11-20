import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.QuotGlue

theorem of_local (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A G : Over S) (Q : A ⟶ G)
    (B : ∀ j, Over (𝒰.X j)) (ψ : ∀ j, (B j).left ⟶ G.left) (q : ∀ j, (Over.pullback (𝒰.f j)).obj A ⟶ B j)
    (hψ : ∀ j, IsPullback (ψ j) (B j).hom G.hom (𝒰.f j))
    (hc : ∀ j, (q j).left ≫ ψ j = pullback.fst A.hom (𝒰.f j) ≫ Q.left)
    (hq : ∀ j, P (q j).left) : P Q.left := by
  have sq : ∀ j, IsPullback (pullback.fst A.hom (𝒰.f j)) (q j).left Q.left (ψ j) := fun j => by
    refine IsPullback.of_bot ?_ (hc j).symm (hψ j)
    have e1 : (q j).left ≫ (B j).hom = pullback.snd A.hom (𝒰.f j) := Over.w (q j)
    have e2 : Q.left ≫ G.hom = A.hom := Over.w Q
    rw [e1, e2]
    exact IsPullback.of_hasPullback _ _
  have hoi : ∀ j, IsOpenImmersion (ψ j) := fun j =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hψ j).flip inferInstance
  have cov : ∀ x : G.left, ∃ j y, ψ j y = x := by
    intro x
    obtain ⟨j, u, hu⟩ := 𝒰.exists_eq (G.hom x)
    obtain ⟨p, hp, -⟩ := Scheme.exists_preimage_of_isPullback (hψ j) x u hu.symm
    exact ⟨j, p, hp⟩
  refine IsZariskiLocalAtTarget.of_openCover (Scheme.Cover.mkOfCovers 𝒰.I₀ (fun j => (B j).left) ψ cov) fun j => ?_
  have h := hq j
  rw [← (sq j).isoPullback_hom_snd, P.cancel_left_of_respectsIso] at h
  exact h

theorem finite_flat_surjective : ∀ (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A G : Over S) (Q : A ⟶ G)
    (B : ∀ j, Over (𝒰.X j)) (ψ : ∀ j, (B j).left ⟶ G.left) (q : ∀ j, (Over.pullback (𝒰.f j)).obj A ⟶ B j),
    (∀ j, IsPullback (ψ j) (B j).hom G.hom (𝒰.f j)) → (∀ j, (q j).left ≫ ψ j = pullback.fst A.hom (𝒰.f j) ≫ Q.left) →
    (∀ j, IsFinite (q j).left) → (∀ j, Flat (q j).left) → (∀ j, Surjective (q j).left) →
    IsFinite Q.left ∧ Flat Q.left ∧ Surjective Q.left := by
  intro S 𝒰 A G Q B ψ q hψ hc hf hfl hs
  have : IsZariskiLocalAtTarget @IsFinite.{0} := by
    set_option backward.isDefEq.respectTransparency.types false in exact inferInstance
  have : IsZariskiLocalAtTarget @Flat.{0} := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat.{0})
  exact ⟨of_local @IsFinite S 𝒰 A G Q B ψ q hψ hc hf, of_local @Flat S 𝒰 A G Q B ψ q hψ hc hfl,
    of_local @Surjective S 𝒰 A G Q B ψ q hψ hc hs⟩

end GlobalTheory.QuotGlue
