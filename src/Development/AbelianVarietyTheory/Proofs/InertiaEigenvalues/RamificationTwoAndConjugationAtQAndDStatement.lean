import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationTwoAndConjugationAtQAndD
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aux_statement : ∀ D : D7, EmbeddingTypeJumps.Conclusion1 D := by
  first | exact @GlobalTheory.PrimesQD.ramification_two_and_conjugation_at_q_and_d | exact GlobalTheory.PrimesQD.ramification_two_and_conjugation_at_q_and_d | (intros; apply GlobalTheory.PrimesQD.ramification_two_and_conjugation_at_q_and_d <;> assumption)
