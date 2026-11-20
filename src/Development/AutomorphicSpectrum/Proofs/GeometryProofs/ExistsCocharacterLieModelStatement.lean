import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCocharacterLieModel
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cocharacter_lie_model : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (R : Type) [CommRing R] (x : Sp R ⟶ S), ∃ M : LieModel (splitTorus S X) x (X →+ R), IsCocharLie M := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusLie.exists_lieModel_splitTorus | exact GlobalTheory.CompanionTheory.Ar.TorusLie.exists_lieModel_splitTorus | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusLie.exists_lieModel_splitTorus <;> assumption)
