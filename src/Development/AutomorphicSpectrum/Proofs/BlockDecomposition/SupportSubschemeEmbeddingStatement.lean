import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportSubschemeEmbedding
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.support_subscheme_embedding : Ysupp.SubEmbedding := by
  first | exact @GlobalTheory.CompanionTheory.SubEmb.subEmbedding | exact GlobalTheory.CompanionTheory.SubEmb.subEmbedding | (intros; apply GlobalTheory.CompanionTheory.SubEmb.subEmbedding <;> assumption)
