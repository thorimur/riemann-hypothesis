import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAdelicGLComplexConjCommutesOperators
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_adelic_GL_complex_conj_commutes_operators : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ C : Sm E a ≃ₗ⋆[ℂ] Sm E a, (∀ φ g, (C φ).1 g = starRingEnd ℂ (φ.1 g)) ∧ ∀ o φ, act o (C φ) = C (act o φ) := by
  first | exact @GlobalTheory.smooth_conj_commutes_act | exact GlobalTheory.smooth_conj_commutes_act | (intros; apply GlobalTheory.smooth_conj_commutes_act <;> assumption)
