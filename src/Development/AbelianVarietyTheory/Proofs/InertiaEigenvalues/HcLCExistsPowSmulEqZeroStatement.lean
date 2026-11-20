import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HcLCExistsPowSmulEqZero
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_smul_eq_zero_of_mem_HcLC_of_torsion : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M) (ϖ : O),
    (∀ m : M, ∃ n : ℕ, ϖ ^ n • m = 0) → ∀ x ∈ ReciprocityTheory.ChartRestriction.T2.HcLC ρ, ∃ n : ℕ, ϖ ^ n • x = 0 := by
  first | exact @GlobalTheory.hcLC_exists_pow_smul_eq_zero | exact GlobalTheory.hcLC_exists_pow_smul_eq_zero | (intros; apply GlobalTheory.hcLC_exists_pow_smul_eq_zero <;> assumption)
