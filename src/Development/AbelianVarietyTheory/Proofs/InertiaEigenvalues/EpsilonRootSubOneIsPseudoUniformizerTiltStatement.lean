import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonRootSubOneIsPseudoUniformizerTilt
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.epsilonRoot_sub_one_isPseudoUniformizer_tilt : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (s : ℕ), ¬ IsUnit (AI.εroot s - 1) ∧ ∀ a : OCb l, a ≠ 0 → ∃ m : ℕ, a ∣ (AI.εroot s - 1) ^ m := by
  first | exact @GlobalTheory.WeakClosed.TiltUnif.main | exact GlobalTheory.WeakClosed.TiltUnif.main | (intros; apply GlobalTheory.WeakClosed.TiltUnif.main <;> assumption)
