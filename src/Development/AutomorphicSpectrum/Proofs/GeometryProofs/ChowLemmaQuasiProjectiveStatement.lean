import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChowLemmaQuasiProjective
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chow_lemma_quasi_projective : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), IsSeparated p → LocallyOfFiniteType p → QuasiCompact p → ∃ (X' : Scheme.{0}) (π : X' ⟶ X), IsProper π ∧ Surjective π ∧ IsQProjOver (π ≫ p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.exists_isProper_surjective_isQProjOver | exact GlobalTheory.CompanionTheory.Ar.Approx.exists_isProper_surjective_isQProjOver | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.exists_isProper_surjective_isQProjOver <;> assumption)
