import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterEtaCondition
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_character_eta_condition : HeckeEta := by
  first | exact @GlobalTheory.CompanionTheory.HeckeEtaExist.heckeEta | exact GlobalTheory.CompanionTheory.HeckeEtaExist.heckeEta | (intros; apply GlobalTheory.CompanionTheory.HeckeEtaExist.heckeEta <;> assumption)
