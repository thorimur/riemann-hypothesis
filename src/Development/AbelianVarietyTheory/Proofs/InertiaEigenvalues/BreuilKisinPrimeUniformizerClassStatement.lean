import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrimeUniformizerClass
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_prime_uniformizer_class : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), Prime (bk.str.symm (Ideal.Quotient.mk _ (X : bk.S))) ∧ intToOC K (bk.str.symm (Ideal.Quotient.mk _ (X : bk.S))) = bk.flat.untilt := by
  first | exact @GlobalTheory.BSP.BK.prime_unif | exact GlobalTheory.BSP.BK.prime_unif | (intros; apply GlobalTheory.BSP.BK.prime_unif <;> assumption)
