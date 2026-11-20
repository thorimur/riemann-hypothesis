import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianVolumeDependsOnlyOnFieldSignature
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_volume_depends_only_on_field_signature : VolumeInvariant := by
  first | exact @GlobalTheory.VolInvariant.volumeInvariant | exact GlobalTheory.VolInvariant.volumeInvariant | (intros; apply GlobalTheory.VolInvariant.volumeInvariant <;> assumption)
