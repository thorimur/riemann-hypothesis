import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

open scoped CategoryTheory.Obj

open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.AbLaw

namespace GlobalTheory.RootTorsion

theorem exists_lift {Y Tb : Scheme.{0}} {t : Tb ⟶ Y} {A : Over Y} {A' : Over Tb} [GrpObj A] [GrpObj A']
    {φ' : A'.left ⟶ A.left} (hpb : IsGrpPullback A' A t φ') {Z' : Over Tb} (x : Over.mk (Z'.hom ≫ t) ⟶ A) :
    ∃ x' : Z' ⟶ A', pushPt hpb.1.w x' = x := by
  refine ⟨Over.homMk (hpb.1.lift x.left Z'.hom (Over.w x)) (hpb.1.lift_snd _ _ _), ?_⟩
  ext
  exact hpb.1.lift_fst _ _ _

end GlobalTheory.RootTorsion
