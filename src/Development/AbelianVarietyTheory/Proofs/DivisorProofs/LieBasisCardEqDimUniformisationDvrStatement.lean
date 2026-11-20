import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBasisCardEqDimUniformisationDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieBasis_card_eq_dim_uniformisation_dvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (IsLocalRing.maximalIdeal V) D A G) (n : ℕ) (y : Fin n → (epsR V ⟶ G)), IsLieBasis y → n = A.g := by
  first | exact @GlobalTheory.LieRankUnif.card_eq_g | exact GlobalTheory.LieRankUnif.card_eq_g | (intros; apply GlobalTheory.LieRankUnif.card_eq_g <;> assumption)
