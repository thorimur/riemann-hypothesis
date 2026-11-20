import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallerUnitaryGroupEmbedding
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smaller_unitary_group_embedding : GlobalTheory.SatakeWeyl.EmbExists := by
  first | exact @GlobalTheory.SatakeWeyl.embExists | exact GlobalTheory.SatakeWeyl.embExists | (intros; apply GlobalTheory.SatakeWeyl.embExists <;> assumption)
