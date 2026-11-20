import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryDepthPairStandardStatement

open GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.SumSize.OppConj

namespace GlobalTheory.SumSize.OppConj

theorem infRowK_main : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → InfRowK :=
  fun hP hI hD hDp => infRowK_of (GlobalTheory.T.dictionary_depth_pair_standard hP hI hD hDp)

end GlobalTheory.SumSize.OppConj
