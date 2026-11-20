import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexConjugateCuspidalRepresentation
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complex_conjugate_cuspidal_representation : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), ∃ (π' : CuspSub E a) (J : π.V ≃ₗ⋆[ℂ] π'.V), ∀ o φ, J (π.op o φ) = π'.op o (J φ) := by
  first | exact @GlobalTheory.exists_conj_cuspSub | exact GlobalTheory.exists_conj_cuspSub | (intros; apply GlobalTheory.exists_conj_cuspSub <;> assumption)
