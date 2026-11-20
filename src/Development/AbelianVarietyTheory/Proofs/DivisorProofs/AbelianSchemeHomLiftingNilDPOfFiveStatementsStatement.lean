import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomLiftingNilDPOfFiveStatements
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianSchemeHomLiftingNilDP_of_hodge_cube_duality_unobstructed : GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianUnobstructed → GlobalTheory.Published.AbelianLifting := by
  first | exact @GlobalTheory.SqLift.abelianLifting_of_known_theorems | exact GlobalTheory.SqLift.abelianLifting_of_known_theorems | (intros; apply GlobalTheory.SqLift.abelianLifting_of_known_theorems <;> assumption)
