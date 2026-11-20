import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCuspidalSatakeParameterStarEqInv
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_cuspidal_satake_parameter_star_eq_inv : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ), (∀ φ ψ, starRingEnd ℂ (H φ ψ) = H ψ φ) → (∀ φ, φ ≠ 0 → 0 < (H φ φ).re) → (∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ) → ∀ (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w (π.locRep w) B → B.map star = B.map (·⁻¹) := by
  first | exact @GlobalTheory.CuspRep.UnitaryParam.map_star_eq_map_inv_of_form | exact GlobalTheory.CuspRep.UnitaryParam.map_star_eq_map_inv_of_form | (intros; apply GlobalTheory.CuspRep.UnitaryParam.map_star_eq_map_inv_of_form <;> assumption)
