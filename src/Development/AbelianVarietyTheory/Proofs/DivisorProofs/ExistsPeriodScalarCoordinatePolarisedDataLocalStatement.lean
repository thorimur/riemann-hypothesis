import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodScalarCoordinatePolarisedDataLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodScalarCoordinate_polarisedData_local : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : GlobalTheory.PolDeg.Data R) (a b : Q.X), ∃ k, Q.TauCoord a b k := by
  first | exact @GlobalTheory.Mum.TensPol.exists_tauCoord | exact GlobalTheory.Mum.TensPol.exists_tauCoord | (intros; apply GlobalTheory.Mum.TensPol.exists_tauCoord <;> assumption)
