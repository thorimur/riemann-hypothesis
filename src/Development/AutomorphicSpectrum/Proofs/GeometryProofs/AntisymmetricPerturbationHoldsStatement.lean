import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AntisymmetricPerturbationHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.antisymmetric_perturbation_holds : GroundTheory.Heights₂.Heights.AntisymPerturbation.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Link.antisymPerturbation_holds | exact GlobalTheory.CompanionTheory.Ar.Link.antisymPerturbation_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Link.antisymPerturbation_holds <;> assumption)
