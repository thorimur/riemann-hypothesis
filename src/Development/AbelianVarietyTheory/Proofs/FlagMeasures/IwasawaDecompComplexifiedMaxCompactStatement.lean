import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompComplexifiedMaxCompact
open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_decomp_complexifiedMaxCompact : IwasawaKC := by
  first | exact @GlobalTheory.Dec.iwasawaKC | exact GlobalTheory.Dec.iwasawaKC | (intros; apply GlobalTheory.Dec.iwasawaKC <;> assumption)
