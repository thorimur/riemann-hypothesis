import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDiagonalFactorizationAlongEmbedding
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_diagonal_factorization_along_embedding : GlobalTheory.SatakeWeyl.EmbTorus := by
  first | exact @GlobalTheory.SatakeWeyl.embTorus | exact GlobalTheory.SatakeWeyl.embTorus | (intros; apply GlobalTheory.SatakeWeyl.embTorus <;> assumption)
