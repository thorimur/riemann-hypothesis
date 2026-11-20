import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoHypothesisGlobalStepAtQd
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKatoHypothesis_globalStep_at_qd : ∀ (D : D7), EmbeddingTypeJumps.admBK (D := D) → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → TruncatedSeriesCountingIdentities.admBK i := by
  first | exact @GlobalTheory.BKAtQD.admBK_embeddingTypeJumps | exact GlobalTheory.BKAtQD.admBK_embeddingTypeJumps | (intros; apply GlobalTheory.BKAtQD.admBK_embeddingTypeJumps <;> assumption)
