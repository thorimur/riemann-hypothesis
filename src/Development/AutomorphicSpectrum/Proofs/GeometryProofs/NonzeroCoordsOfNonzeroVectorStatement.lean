import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonzeroCoordsOfNonzeroVector
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonzero_coords_of_nonzero_vector : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ) (x : D.B.carrier) (c : Fin D.g → ℂ), D.len σ x ^ 2 = Real.pi * (a.herm c c).re → x ≠ 0 → c ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.FrameZero.coord_ne_zero | exact GlobalTheory.CompanionTheory.Ar.Sl.FrameZero.coord_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.FrameZero.coord_ne_zero <;> assumption)
