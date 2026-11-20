import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_firstDeRham_structure : GlobalTheory.Published.AbelianDeRham := by
  first | exact @GlobalTheory.abelianDeRham | exact GlobalTheory.abelianDeRham | (intros; apply GlobalTheory.abelianDeRham <;> assumption)
