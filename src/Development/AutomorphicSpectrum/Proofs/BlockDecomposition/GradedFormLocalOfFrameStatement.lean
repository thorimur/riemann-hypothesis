import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormLocalOfFrame
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_form_local_of_frame : GlobalTheory.CompanionTheory.GrForm.StFrame → CrystallineSemistableComparison.Pb.KH.LocGr → CrystallineSemistableComparison.Pb.KH.PolyTf → GlobalTheory.CompanionTheory.GrForm.StLoc := by
  first | exact @GlobalTheory.CompanionTheory.GrForm.stLoc | exact GlobalTheory.CompanionTheory.GrForm.stLoc | (intros; apply GlobalTheory.CompanionTheory.GrForm.stLoc <;> assumption)
