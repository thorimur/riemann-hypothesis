import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDualityClassFieldFactsOfArtinTateEuler

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_duality_class_field_facts_of_artin_tate_euler : GlobalTheory.Published.GlobalArtinReciprocity → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ReciprocityTheory.ChartRestriction.T2.Core := by
  first | exact @GlobalTheory.langRecCore_of_artinReciprocity | exact GlobalTheory.langRecCore_of_artinReciprocity | (intros; apply GlobalTheory.langRecCore_of_artinReciprocity <;> assumption)
