import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.OpenImmersion
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
import Mathlib.RingTheory.WittVector.IsPoly
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

namespace AlgebraicGeometry

open CategoryTheory

universe u

namespace IsOpenImmersion

theorem bijective_appLE_of_image_eq {A B : Scheme.{u}} (f : A ⟶ B) [IsOpenImmersion f]
    (O : B.Opens) (S : A.Opens) (e : S ≤ f ⁻¹ᵁ O) (h : f ''ᵁ S = O) :
    Function.Bijective (CommRingCat.Hom.hom (Scheme.Hom.appLE f O S e)) := by
  subst h
  have : IsIso (Scheme.Hom.appLE f (f ''ᵁ S) S e) := by
    rw [← Scheme.Hom.appIso_hom' f S]
    infer_instance
  constructor
  · intro a b hab
    have h1 : (CommRingCat.Hom.hom (Scheme.Hom.appLE f (f ''ᵁ S) S e ≫
          inv (Scheme.Hom.appLE f (f ''ᵁ S) S e))) a
        = (CommRingCat.Hom.hom (Scheme.Hom.appLE f (f ''ᵁ S) S e ≫
          inv (Scheme.Hom.appLE f (f ''ᵁ S) S e))) b := by
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, hab]
    rw [IsIso.hom_inv_id] at h1
    simpa only [CommRingCat.hom_id, RingHom.id_apply] using h1
  · intro y
    refine ⟨(CommRingCat.Hom.hom (inv (Scheme.Hom.appLE f (f ''ᵁ S) S e))) y, ?_⟩
    have h3 := congrArg (fun mm => (CommRingCat.Hom.hom mm) y)
      (IsIso.inv_hom_id (Scheme.Hom.appLE f (f ''ᵁ S) S e))
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id,
      RingHom.id_apply] using h3

end IsOpenImmersion

end AlgebraicGeometry
