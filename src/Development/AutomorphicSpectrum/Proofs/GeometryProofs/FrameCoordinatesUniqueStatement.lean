import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameCoordinatesUnique
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_coordinates_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ), (∀ v, IsTangent v → ∃! w, a.u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ a.u.IsDiff w v) → ∀ x : D.B.carrier, ∃! c, D.IsVec a x c := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.FrameVec.isVec_existsUnique | exact GlobalTheory.CompanionTheory.Ar.Sl.FrameVec.isVec_existsUnique | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.FrameVec.isVec_existsUnique <;> assumption)
