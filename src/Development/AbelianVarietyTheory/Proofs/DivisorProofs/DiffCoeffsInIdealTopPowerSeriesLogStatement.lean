import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffCoeffsInIdealTopPowerSeriesLog
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diffCoeffsInIdeal_top_powerSeries_log : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q], DIn (⊤ : Ideal B) (PowerSeries.log Q : MvPowerSeries Unit Q) := by
  first | exact @GlobalTheory.QLog.LogDiff.dIn_log | exact GlobalTheory.QLog.LogDiff.dIn_log | (intros; apply GlobalTheory.QLog.LogDiff.dIn_log <;> assumption)
