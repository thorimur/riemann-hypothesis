import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumCountBoundLargeDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosineCountOfPublishedInputsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorCountBoundOfCosetDepthBound

open GlobalTheory.SumSize GlobalTheory.RowClaim

namespace GlobalTheory.SumCount

theorem infCountK : GlobalTheory.FunPr.Hypotheses₂ → DepthK → InfCountK := fun hP hD =>
  infCountK_of GlobalTheory.T.datumCountBound_largeData (GlobalTheory.T.cosine_count_of_hypotheses hP) (GlobalTheory.T.pureTensorCountBound_of_cosetDepthBound hD)

end GlobalTheory.SumCount
