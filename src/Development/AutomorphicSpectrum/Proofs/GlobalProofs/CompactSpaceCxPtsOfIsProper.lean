import Development.WeilBound.CoreStatements.ProjectiveValuations.CompactSpaceComplexPointsOfProper
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.Gaga

theorem compactSpace_cxPts_of_isProper :
    ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ), IsProper p → CompactSpace (CxPts p (RingHom.id ℂ)) :=
  DifferentiableLines.compactSpace_complex_points_of_proper

end GlobalTheory.CompanionTheory.Gaga
