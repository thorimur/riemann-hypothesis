import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHens
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.BtExistsBc
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatBcPull
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopf

namespace PositivityTheory.HtPt.Htat

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct in
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge in
theorem bt_sub_eq_top : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.btOrder U = Γ.btOrder ⊤ :=
  @bt_sub_eq_top_of @hens_normal @PositivityTheory.UnitarySelfGeneration.bt_exists_bc @reg_pull

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct in
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge in
theorem bt_hopf : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), IsHopfOrder (Γ.btOrder ⊤) :=
  @bt_hopf_of @hens_normal @PositivityTheory.UnitarySelfGeneration.bt_exists_bc @reg_pull

end PositivityTheory.HtPt.Htat
