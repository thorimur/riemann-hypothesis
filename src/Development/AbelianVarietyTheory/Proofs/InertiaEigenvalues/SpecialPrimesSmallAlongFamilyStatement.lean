import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialPrimesSmallAlongFamily
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specialPrimes_small_along_family : ∀ {eps : ℝ} (Fm : FamP eps), ∀ C : ℝ, 1 ≤ C → ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, Small (Fm.L x i) C ∧ 8 ≤ (Fm.L x i).sc.L ∧ 60 ≤ (Fm.D x i).host.splitBound ∧ C ≤ (Fm.L x i).sc.b := by
  first | exact @GlobalTheory.SpecialSmall.special_primes_small | exact GlobalTheory.SpecialSmall.special_primes_small | (intros; apply GlobalTheory.SpecialSmall.special_primes_small <;> assumption)
