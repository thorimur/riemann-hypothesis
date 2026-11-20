import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonzeroSectionGenericFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonzero_section_generic_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (M : LB G.left), M.IsLB → ∀ t : SecMod G.hom M, t ≠ 0 → ∀ b : Sp R, b.asIdeal = ⊥ → ∃ y : G.left, G.hom y = b ∧ y ∈ Out.nonzeroLocus (M := M) t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Gen.exists_generic_mem_nonzeroLocus | exact GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Gen.exists_generic_mem_nonzeroLocus | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Gen.exists_generic_mem_nonzeroLocus <;> assumption)
