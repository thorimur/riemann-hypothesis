import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperSemicontinuousLimsupExt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperSemicontinuous_limsupExt : ∀ (Y : Type) [TopologicalSpace Y] (S : Set Y) (u : Y → ℝ), UpperSemicontinuous (GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.limsupExt S u) := by
  first | exact @GlobalTheory.limsupExt_usc_all | exact GlobalTheory.limsupExt_usc_all | (intros; apply GlobalTheory.limsupExt_usc_all <;> assumption)
