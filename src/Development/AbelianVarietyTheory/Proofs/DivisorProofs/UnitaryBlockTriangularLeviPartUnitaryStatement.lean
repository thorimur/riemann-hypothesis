import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryBlockTriangularLeviPartUnitary
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_block_triangular_levi_part_unitary : GlobalTheory.SatakeWeyl.LeviPart := by
  first | exact @GlobalTheory.SatakeWeyl.leviPart | exact GlobalTheory.SatakeWeyl.leviPart | (intros; apply GlobalTheory.SatakeWeyl.leviPart <;> assumption)
