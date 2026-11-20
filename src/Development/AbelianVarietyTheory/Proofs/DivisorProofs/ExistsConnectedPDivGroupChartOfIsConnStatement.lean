import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectedPDivGroupChartOfIsConn
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_connectedPDivGroupChart_of_isConn : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), G.IsConn → ∃ d, Nonempty (Chart G d) := by
  first | exact @GlobalTheory.Katz.exists_chart_of_isConn | exact GlobalTheory.Katz.exists_chart_of_isConn | (intros; apply GlobalTheory.Katz.exists_chart_of_isConn <;> assumption)
