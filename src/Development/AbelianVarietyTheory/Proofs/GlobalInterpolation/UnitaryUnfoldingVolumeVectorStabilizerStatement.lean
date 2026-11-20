import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryUnfoldingVolumeVectorStabilizer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryUnfolding_volume_vectorStabilizer : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.QuotientMeasures → GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure.AdelicUnitaryHaar → GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive → ∀ D : Formalism.BasicNotions.D7, GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.Unfolding D := by
  first | exact @GlobalTheory.VolumeUnfolding.unfolding | exact GlobalTheory.VolumeUnfolding.unfolding | (intros; apply GlobalTheory.VolumeUnfolding.unfolding <;> assumption)
