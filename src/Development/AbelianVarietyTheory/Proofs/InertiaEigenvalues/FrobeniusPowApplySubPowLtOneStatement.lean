import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPowApplySubPowLtOne
open NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_pow_apply_sub_pow_lt_one : ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω) (q : ℕ) (σ : Ω ≃ₐ[F] Ω),
    Formalism.ConjugateSelfDual.IsFrob A q σ → ∀ (n : ℕ) (x : Ω), A.valuation x ≤ 1 → A.valuation ((σ ^ n) x - x ^ (q ^ n)) < 1 := by
  first | exact @GlobalTheory.frob_pow_apply_sub_lt_one | exact GlobalTheory.frob_pow_apply_sub_lt_one | (intros; apply GlobalTheory.frob_pow_apply_sub_lt_one <;> assumption)
