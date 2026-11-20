import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

def TwoTorsRat {R : Type} [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] : Prop :=
  ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (x : Over.mk (spMap (algebraMap (FractionRing R) F) ≫ jK R) ⟶ G),
    x * x = 1 → ∃ y : Over.mk (jK R) ⟶ G, x.left = spMap (algebraMap (FractionRing R) F) ≫ y.left

def SplitClosed {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] : Prop :=
  ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X),
    Nonempty (GlobalTheory.UU.TQ (thickObj R (maximalIdeal R) 0 G) X)

end GlobalTheory.Mum
