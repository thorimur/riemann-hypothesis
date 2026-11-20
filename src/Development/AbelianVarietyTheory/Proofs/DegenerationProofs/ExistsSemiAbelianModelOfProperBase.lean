import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Mathlib.AlgebraicGeometry.ValuativeCriterion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem exists_semiAbelian_model_of_proper_base :
    ∀ (o W L : Type) [CommRing o] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (β : o →+* W) (Z : Scheme.{0}) (s : Z ⟶ Sp o) (x : Sp L ⟶ Z) (G : Over Z) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left), IsProper s → x ≫ s = spMap ((algebraMap W L).comp β) → IsSemiAbelian G → IsGrpPullback A G x φ → ∃ (G' : Over (Sp W)) (_ : GrpObj G') (e : (Over.pullback (spMap (algebraMap W L))).obj G' ≅ A), IsSemiAbelian G' ∧ IsMonHom e.hom := by
  intro o W L _ _ _ _ _ _ _ β Z s x G _ A _ φ hs hx hG hA
  have hE : ValuativeCriterion.Existence s :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) s).1
  have hw : x ≫ s = Spec.map (CommRingCat.ofHom (algebraMap W L)) ≫ spMap β := by
    rw [hx, ← Spec.map_comp]; rfl
  obtain ⟨⟨y, hy, -⟩⟩ := (hE { R := W, K := L, i₁ := x, i₂ := spMap β, commSq := ⟨hw⟩ }).exists_lift
  have hy' : spMap (algebraMap W L) ≫ y = x := hy
  obtain ⟨e, he, -⟩ := grpPullback_iso
    (((isGrpPullback_pullback ((Over.pullback y).obj G) (spMap (algebraMap W L))).comp
      (isGrpPullback_pullback G y)).congr hy' rfl) hA
  exact ⟨(Over.pullback y).obj G, inferInstance, e, IsSemiAbelian.pullback y G hG, he⟩

end GlobalTheory.SS
