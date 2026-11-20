import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallerUnitaryEmbeddingPreservesIntegralParts
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smaller_unitary_embedding_preserves_integral_parts : GlobalTheory.SatakeWeyl.EmbMem := by
  first | exact @GlobalTheory.SatakeWeyl.embMem | exact GlobalTheory.SatakeWeyl.embMem | (intros; apply GlobalTheory.SatakeWeyl.embMem <;> assumption)
