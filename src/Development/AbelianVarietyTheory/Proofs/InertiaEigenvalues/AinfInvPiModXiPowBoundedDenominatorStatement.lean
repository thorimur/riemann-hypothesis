import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfInvPiModXiPowBoundedDenominator
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_invPi_mod_xi_pow_bounded_denominator : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (k n M : ℕ), 1 ≤ M → k ≤ (l - 1) * n → ((l : ℕ) : Ainf l) ^ (n + M - 1) ∈ Ideal.span {AI.π₁ ^ k, AI.ξ ^ M} := by
  first | exact @GlobalTheory.Adopt.ainf_invPi_mod_xi_pow_bounded_denominator | exact GlobalTheory.Adopt.ainf_invPi_mod_xi_pow_bounded_denominator | (intros; apply GlobalTheory.Adopt.ainf_invPi_mod_xi_pow_bounded_denominator <;> assumption)
