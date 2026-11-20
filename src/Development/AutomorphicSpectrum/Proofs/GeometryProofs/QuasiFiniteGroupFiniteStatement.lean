import Development.AutomorphicSpectrum.Proofs.GeometryProofs.QuasiFiniteGroupFinite
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasi_finite_group_finite : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T), Finite T := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.QFGroup.finite_of_qfGroup | exact GlobalTheory.CompanionTheory.Ar.BT.QFGroup.finite_of_qfGroup | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.QFGroup.finite_of_qfGroup <;> assumption)
