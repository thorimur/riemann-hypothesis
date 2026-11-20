import Development.WeilBound.CoreStatements.HodgeTatePoints.TorsrepEx
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem torsRep_nonempty_of_relAmple : ∀ (R : Type) [CommRing R] [IsLocalRing R] (p : ℕ), 1 ≤ p → ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → Nonempty (TorsRep A p) :=
  PositivityTheory.HtPt.Rg.torsrep_ex

end GlobalTheory.CompanionTheory.Ar.GR
