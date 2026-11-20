import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDualCrystalOfHyp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineSmoothLiftOfRelations

namespace GlobalTheory

theorem abelianDualCrystal_of_dualAbelianScheme :
    GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.AbelianDualCrystal :=
  fun h => GlobalTheory.abelianDualCrystal_of_dual_of_smoothLift h GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations

end GlobalTheory
