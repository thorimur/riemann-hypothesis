import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeMeasureLocallyFinite
open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise
open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_measure_locally_finite : ∀ n : ℕ, coneMeas n ≠ 0 ∧ ∀ C : Set (Fin n × Fin n → ℝ), IsCompact C → C ⊆ PositivityTheory.RgBcC.cone n → coneMeas n C < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.ConeHaar.Fin.coneMeas_ne_zero_and_lt_top | exact GlobalTheory.CompanionTheory.ConeHaar.Fin.coneMeas_ne_zero_and_lt_top | (intros; apply GlobalTheory.CompanionTheory.ConeHaar.Fin.coneMeas_ne_zero_and_lt_top <;> assumption)
