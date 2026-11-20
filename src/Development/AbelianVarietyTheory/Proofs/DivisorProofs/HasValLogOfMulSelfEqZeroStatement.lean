import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasValLogOfMulSelfEqZero
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasVal_log_of_mul_self_eq_zero' : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q] (p : ℕ) (x : B), x * x = 0 → HasVal p (fun _ : Unit => x) (PowerSeries.log Q : MvPowerSeries Unit Q) (algebraMap B Q x) := by
  first | exact @GlobalTheory.QLog.SqZero.hasVal_log_of_mul_self_eq_zero | exact GlobalTheory.QLog.SqZero.hasVal_log_of_mul_self_eq_zero | (intros; apply GlobalTheory.QLog.SqZero.hasVal_log_of_mul_self_eq_zero <;> assumption)
