import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFourierBoundSeminorm
open MeasureTheory Matrix
open Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.GodementFE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_fourier_bound_seminorm : ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (f : SchwartzMap (Fin 2 → ℂ) ℂ) (x ξ : ℂ),
    ‖sF f x ξ‖ ≤ C * pS N f * (dd x * dd ξ) := by
  first | exact @GlobalTheory.CompanionTheory.GodementFE.Unif.sF_decay_unif | exact GlobalTheory.CompanionTheory.GodementFE.Unif.sF_decay_unif | (intros; apply GlobalTheory.CompanionTheory.GodementFE.Unif.sF_decay_unif <;> assumption)
