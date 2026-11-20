import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffBoundaryComplementVolumeZero
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open AlgebraicGeometry CategoryTheory MeasureTheory Set GlobalTheory.ShFam GlobalTheory.ChernReg GlobalTheory.CxPts GlobalTheory.TrueGeo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ProjVar Formalism.L2.Pj Formalism.L2.Geo GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.off_boundary_complement_volume_zero : OnCore fun D O _ _ => ∀ c (σ : D.what₂.LL →+* ℂ) (ch : AlgChart (O.var c).str σ (O.var c).dim), MeasureTheory.volume (ch.e '' ((offBd O.Φ c σ)ᶜ ∩ ch.e.source)) = 0 := by
  first | exact @GlobalTheory.BoundaryNull.volume_chart_image_compl_offBd | exact GlobalTheory.BoundaryNull.volume_chart_image_compl_offBd | (intros; apply GlobalTheory.BoundaryNull.volume_chart_image_compl_offBd <;> assumption)
