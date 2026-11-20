import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WordLengthBoundOfLinear
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.word_length_bound_of_linear : DsLin → WordBd := by
  first | exact @GlobalTheory.CompanionTheory.BmuWordBd.wordBd_of_dsLin | exact GlobalTheory.CompanionTheory.BmuWordBd.wordBd_of_dsLin | (intros; apply GlobalTheory.CompanionTheory.BmuWordBd.wordBd_of_dsLin <;> assumption)
