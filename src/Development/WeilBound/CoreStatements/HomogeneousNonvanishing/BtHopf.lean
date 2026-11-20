import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHens
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatBcPull
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.BtExistsBc
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopf
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace PositivityTheory.UnitarySelfGeneration

theorem bt_sub_eq_top : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.btOrder U = Γ.btOrder ⊤ :=
  PositivityTheory.HtPt.Htat.bt_sub_eq_top_of PositivityTheory.HtPt.Htat.hens_normal PositivityTheory.UnitarySelfGeneration.bt_exists_bc PositivityTheory.HtPt.Htat.reg_pull

theorem bt_hopf : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), IsHopfOrder (Γ.btOrder ⊤) :=
  PositivityTheory.HtPt.Htat.bt_hopf_of PositivityTheory.HtPt.Htat.hens_normal PositivityTheory.UnitarySelfGeneration.bt_exists_bc PositivityTheory.HtPt.Htat.reg_pull

end PositivityTheory.UnitarySelfGeneration
