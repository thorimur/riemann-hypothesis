import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinimalPrimesOfMultihomogSup
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minimal_primes_of_multihomog_sup : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)), IsMultiHomogIdeal P → IsMultiHomogIdeal D → ∀ Q ∈ (P ⊔ D).minimalPrimes, IsMultiHomogIdeal Q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.MinHom.isMultiHomogIdeal_of_mem_minimalPrimes_sup | exact GlobalTheory.CompanionTheory.Ar.Cmp.MinHom.isMultiHomogIdeal_of_mem_minimalPrimes_sup | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.MinHom.isMultiHomogIdeal_of_mem_minimalPrimes_sup <;> assumption)
