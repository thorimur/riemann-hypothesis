import Development.AutomorphicSpectrum.Proofs.AdelicProofs.SumLogIdealEqLogAbsNorm
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_logIdeal_eq_log_absNorm : ∀ (E : Type) [Field E] [NumberField E] (I : Ideal (𝓞 E)), I ≠ ⊥ → ∀ p : Nat.Primes, ∑ j : E →+* ℂ_[p], logIdeal (j.comp (algebraMap (𝓞 E) E)) I = Real.log ‖((Ideal.absNorm I : ℕ) : ℂ_[p])‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.sum_logIdeal_eq_log_norm_absNorm | exact GlobalTheory.CompanionTheory.Ar.Fl.sum_logIdeal_eq_log_norm_absNorm | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.sum_logIdeal_eq_log_norm_absNorm <;> assumption)
