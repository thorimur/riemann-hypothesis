import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulLtFinrankCyclotomicAtQAndD
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mul_lt_finrank_cyclotomic_at_q_and_d : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → D.R.t * D.R.r < Module.finrank D.host.E (CyclotomicField (D.nd.l i) D.host.E) := by
  first | exact @GlobalTheory.CycDegRam.tr_lt_finrank_cyclotomic | exact GlobalTheory.CycDegRam.tr_lt_finrank_cyclotomic | (intros; apply GlobalTheory.CycDegRam.tr_lt_finrank_cyclotomic <;> assumption)
