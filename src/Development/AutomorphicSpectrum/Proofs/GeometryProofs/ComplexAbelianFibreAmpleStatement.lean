import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexAbelianFibreAmple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_abelian_fibre_ample : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ), ∃ (t' : SAB H (Sp ℂ)) (_ : SABMap t' D.t (emb σ)), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.FibrePol.exists_fibre_pol | exact GlobalTheory.CompanionTheory.Ar.Sl.FibrePol.exists_fibre_pol | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.FibrePol.exists_fibre_pol <;> assumption)
