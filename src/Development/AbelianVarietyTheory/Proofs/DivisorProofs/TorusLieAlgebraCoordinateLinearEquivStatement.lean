import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusLieAlgebraCoordinateLinearEquiv
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_lie_algebra_coordinate_linear_equiv : ∀ (R : Type) [CommRing R] (r : ℕ), Function.Bijective (lieCoord : LieG (torus R r) → Fin r → R) ∧ (∀ x y : LieG (torus R r), lieCoord (lieAdd _ x y) = lieCoord x + lieCoord y) ∧ ∀ (a : R) (x : LieG (torus R r)), lieCoord (lieScale _ a x) = a • lieCoord x := by
  first | exact @GlobalTheory.TorusLieCoord.lieCoord_bijective_add_smul | exact GlobalTheory.TorusLieCoord.lieCoord_bijective_add_smul | (intros; apply GlobalTheory.TorusLieCoord.lieCoord_bijective_add_smul <;> assumption)
