import Development.WeilBound.CoreStatements.HodgeTatePoints.RiOact

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem polAV_oAct_int : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] (P : Out.PolAV (Geo.Tor.Sp O)), Nonempty (P.OAct ℤ) :=
  @PositivityTheory.HtPt.Ri.oact_int

end GlobalTheory.CompanionTheory.Ar.GR
