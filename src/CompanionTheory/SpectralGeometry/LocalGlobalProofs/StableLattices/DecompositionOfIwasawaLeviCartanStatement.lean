import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfIwasawaLeviCartan
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decomposition_of_iwasawa_levi_cartan : AdaptExists → IwaQ → LeviQ → CartanQ → Decomp := by
  first | exact @GlobalTheory.CompanionTheory.BmuDecomp.decomp | exact GlobalTheory.CompanionTheory.BmuDecomp.decomp | (intros; apply GlobalTheory.CompanionTheory.BmuDecomp.decomp <;> assumption)
