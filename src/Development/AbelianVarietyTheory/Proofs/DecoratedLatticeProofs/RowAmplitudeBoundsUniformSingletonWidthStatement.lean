import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowAmplitudeBoundsUniformSingletonWidth
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowAmplitudeBoundsUniform_singleton_width : ∀ c : ℝ, AmpOn {c} := by
  first | exact @GlobalTheory.AmpRecordGap.ampOn_singleton | exact GlobalTheory.AmpRecordGap.ampOn_singleton | (intros; apply GlobalTheory.AmpRecordGap.ampOn_singleton <;> assumption)
