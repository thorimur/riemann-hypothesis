import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffCutoff
open Filter Topology Set Metric MeasureTheory GlobalTheory.ChernReg
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_cutoff' : ContDiff ℝ ∞ GlobalTheory.ChernReg.cutoff := by
  first | exact @GlobalTheory.ChernReg.contDiff_cutoff | exact GlobalTheory.ChernReg.contDiff_cutoff | (intros; apply GlobalTheory.ChernReg.contDiff_cutoff <;> assumption)
