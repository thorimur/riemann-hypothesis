import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.OrdinaryCurveOfHodgeTate
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PtEqOneOfGZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem ordinaryCurveStatement : GlobalTheory.CompanionTheory.Ar.GR.OrdinaryCurveStatement :=
  GlobalTheory.CompanionTheory.Ar.GR.ordinaryCurve_of_hodgeTate GlobalTheory.CompanionTheory.Ar.GR.Top.main

end GlobalTheory.CompanionTheory.Ar.Link
