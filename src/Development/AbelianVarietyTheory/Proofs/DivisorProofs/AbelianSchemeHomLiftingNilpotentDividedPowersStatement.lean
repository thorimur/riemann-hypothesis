import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomLiftingNilpotentDividedPowers
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.print_abelianLifting : GlobalTheory.Published.AbelianLifting := by
  first | exact @GlobalTheory.abelianScheme_hom_lifting_nilpotent_dividedPowers | exact GlobalTheory.abelianScheme_hom_lifting_nilpotent_dividedPowers | (intros; apply GlobalTheory.abelianScheme_hom_lifting_nilpotent_dividedPowers <;> assumption)
