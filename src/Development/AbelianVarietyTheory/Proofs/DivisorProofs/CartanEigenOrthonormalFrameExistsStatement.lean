import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExists
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartanEigen_orthonormalFrame_exists : GlobalTheory.RealLift.FrameEx := by
  first | exact @GlobalTheory.RealLift.frameEx_holds | exact GlobalTheory.RealLift.frameEx_holds | (intros; apply GlobalTheory.RealLift.frameEx_holds <;> assumption)
