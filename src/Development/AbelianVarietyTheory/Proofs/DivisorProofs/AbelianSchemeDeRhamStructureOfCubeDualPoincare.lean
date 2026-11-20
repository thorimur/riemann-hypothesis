import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamOfHyp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineSmoothLiftOfRelations

namespace GlobalTheory

theorem abelianDeRham_of_hodge_cube_dual_poincare :
    GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.DualAbelianScheme →
      GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianDeRham :=
  GlobalTheory.abelianDeRham_of_crystallineSmoothLift GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations

end GlobalTheory
