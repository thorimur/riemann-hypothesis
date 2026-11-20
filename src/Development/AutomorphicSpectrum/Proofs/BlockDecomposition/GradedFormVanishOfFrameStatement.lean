import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormVanishOfFrame
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_form_vanish_of_frame : GlobalTheory.CompanionTheory.GrForm.StFrame → CrystallineSemistableComparison.Pb.KH.LocGr → CrystallineSemistableComparison.Pb.KH.PolyTf → GlobalTheory.CompanionTheory.GrForm.StVan := by
  first | exact @GlobalTheory.CompanionTheory.GrForm.van | exact GlobalTheory.CompanionTheory.GrForm.van | (intros; apply GlobalTheory.CompanionTheory.GrForm.van <;> assumption)
