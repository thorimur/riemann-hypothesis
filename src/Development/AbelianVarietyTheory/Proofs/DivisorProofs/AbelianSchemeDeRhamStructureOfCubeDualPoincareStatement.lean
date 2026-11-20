import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamStructureOfCubeDualPoincare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianSchemeDeRhamStructure_of_cube_dual_poincare : GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianDeRham := by
  first | exact @GlobalTheory.abelianDeRham_of_hodge_cube_dual_poincare | exact GlobalTheory.abelianDeRham_of_hodge_cube_dual_poincare | (intros; apply GlobalTheory.abelianDeRham_of_hodge_cube_dual_poincare <;> assumption)
