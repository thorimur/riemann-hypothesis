import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SqrtNegPrimeNotMemMaxUnramified
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sqrt_neg_prime_not_mem_max_unramified : ∀ (l : ℕ) [Fact l.Prime] (y : Om l), y ^ 2 = -(l : Om l) → y ∉ MaximalUnramifiedExtension l := by
  first | exact @GlobalTheory.sqrt_neg_l_not_mem_Kur | exact GlobalTheory.sqrt_neg_l_not_mem_Kur | (intros; apply GlobalTheory.sqrt_neg_l_not_mem_Kur <;> assumption)
