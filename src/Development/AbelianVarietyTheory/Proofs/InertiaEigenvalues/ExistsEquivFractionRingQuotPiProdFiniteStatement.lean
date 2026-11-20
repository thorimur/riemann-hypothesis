import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivFractionRingQuotPiProdFinite
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_fractionRingQuot_pi_prod_finite : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}, Irreducible ϖ →
    ∀ {Y : Type} [AddCommGroup Y] [Module O Y], (∀ y : Y, ∃ n : ℕ, ϖ ^ n • y = 0) →
    Finite (LinearMap.ker (ϖ • LinearMap.id : Y →ₗ[O] Y)) →
    ∃ (a : ℕ) (F : Type) (_ : AddCommGroup F) (_ : Module O F), Finite F ∧ Nonempty (Y ≃ₗ[O] (Fin a → Formalism.NG.KO O) × F) := by
  first | exact @GlobalTheory.CofinGen.exists_equiv_pi_prod_finite | exact GlobalTheory.CofinGen.exists_equiv_pi_prod_finite | (intros; apply GlobalTheory.CofinGen.exists_equiv_pi_prod_finite <;> assumption)
