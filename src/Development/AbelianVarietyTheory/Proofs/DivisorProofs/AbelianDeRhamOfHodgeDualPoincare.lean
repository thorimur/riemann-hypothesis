import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamStructureOfCubeDualPoincareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBaseStatement

namespace GlobalTheory

theorem abelianDeRham_of_hodge_dual_poincare :
    GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.DualAbelianScheme →
      GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianDeRham :=
  fun h₁ h₂ h₃ => GlobalTheory.T.abelianSchemeDeRhamStructure_of_cube_dual_poincare h₁ GlobalTheory.T.theoremOfCubeAbelianScheme_over_arbitrary_base h₂ h₃

end GlobalTheory
