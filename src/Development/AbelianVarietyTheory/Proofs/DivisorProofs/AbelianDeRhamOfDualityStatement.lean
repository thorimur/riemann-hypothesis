import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamOfDuality
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_de_rham_of_duality : GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.AbelianDeRhamStructure → GlobalTheory.Published.CrystallineDeRham → GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianDeRham := by
  first | exact @GlobalTheory.abelianDeRham_of_duality | exact GlobalTheory.abelianDeRham_of_duality | (intros; apply GlobalTheory.abelianDeRham_of_duality <;> assumption)
