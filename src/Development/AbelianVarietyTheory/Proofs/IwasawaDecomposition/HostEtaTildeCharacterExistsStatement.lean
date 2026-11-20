import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostEtaTildeCharacterExists
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.host_etaTilde_character_exists : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), EtaTExists H := by
  first | exact @GlobalTheory.Mem.EtaT.etaT_exists | exact GlobalTheory.Mem.EtaT.etaT_exists | (intros; apply GlobalTheory.Mem.EtaT.etaT_exists <;> assumption)
