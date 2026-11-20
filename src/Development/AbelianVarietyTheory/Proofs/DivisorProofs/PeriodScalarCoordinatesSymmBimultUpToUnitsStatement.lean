import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodScalarCoordinatesSymmBimultUpToUnits
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodScalarCoordinates_symm_bimult_up_to_units : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : GlobalTheory.PolDeg.Data R) (k : Q.X → Q.X → (FractionRing R)ˣ), (∀ a b, Q.TauCoord a b (k a b)) → (∀ a b, ∃ u ∈ unitsK R, k b a = u * k a b) ∧ ∀ a a' b, ∃ u ∈ unitsK R, k (a + a') b = u * (k a b * k a' b) := by
  first | exact @GlobalTheory.Mum.TensPolRel.tauCoord_rel | exact GlobalTheory.Mum.TensPolRel.tauCoord_rel | (intros; apply GlobalTheory.Mum.TensPolRel.tauCoord_rel <;> assumption)
