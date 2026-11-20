import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIndexLeftRightCosetSumsEq
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_index_left_right_coset_sums_eq : GlobalTheory.SatakeWeyl.UnimodFin := by
  first | exact @GlobalTheory.SatakeWeyl.unimodFin | exact GlobalTheory.SatakeWeyl.unimodFin | (intros; apply GlobalTheory.SatakeWeyl.unimodFin <;> assumption)
