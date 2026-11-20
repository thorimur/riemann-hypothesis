import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstOneAddXPowLogEqNsmul
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subst_one_add_X_pow_log_eq_nsmul : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q] (m : ℕ), subst (up Q (fun _ : Unit => ((1 + X ()) ^ m - 1 : MvPowerSeries Unit B))) (PowerSeries.log Q : MvPowerSeries Unit Q) = (m : Q) • (PowerSeries.log Q : MvPowerSeries Unit Q) := by
  first | exact @GlobalTheory.Proof.subst_one_add_X_pow_log_eq_nsmul.subst_pow_log | exact GlobalTheory.Proof.subst_one_add_X_pow_log_eq_nsmul.subst_pow_log | (intros; apply GlobalTheory.Proof.subst_one_add_X_pow_log_eq_nsmul.subst_pow_log <;> assumption)
