import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliOperatorAlgebraStableUnderComplexConj
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_operator_algebra_stable_under_complex_conj : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (C : Sm E a ≃ₗ⋆[ℂ] Sm E a), (∀ o φ, act o (C φ) = C (act o φ)) → ∀ z ∈ Zalg E a, ∃ z' ∈ Zalg E a, ∀ φ, z (C φ) = C (z' φ) := by
  first | exact @GlobalTheory.CuspRep.ConjZalg.conj_Zalg | exact GlobalTheory.CuspRep.ConjZalg.conj_Zalg | (intros; apply GlobalTheory.CuspRep.ConjZalg.conj_Zalg <;> assumption)
