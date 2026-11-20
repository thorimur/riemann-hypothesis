import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesisBundleConversions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaDenominatorsFitFunction

namespace GlobalTheory.BigTop.Fun.Close

theorem fun0Fit_of_join : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Mem.LiteralAutomorphy.JoinOut → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate → GlobalTheory.BigTop.LamLow → GlobalTheory.BigTop.Fun.Fun0Fit @GlobalTheory.BigTop.Fun.Fld := by
  intro hP hJ hHT hTheta hLoc hSep hLam
  obtain ⟨hTD, hTr, hTw, hZD, hRefl⟩ :=
    hJ
  exact GlobalTheory.BigTop.Fun.Close.fun0Fit_close hP (GlobalTheory.Published.HeckeTateFunctionalEquation.abs hHT) hTD hTr hTw hZD hRefl
    hTheta hLoc hSep hLam

end GlobalTheory.BigTop.Fun.Close
