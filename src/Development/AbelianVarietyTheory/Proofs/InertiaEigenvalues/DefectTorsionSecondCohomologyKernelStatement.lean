import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefectTorsionSecondCohomologyKernel
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.defect_torsion_second_cohomology_kernel : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), Pr2d D HW F := by
  first | exact @GlobalTheory.NL.DefectTorsion.defect_torsion | exact GlobalTheory.NL.DefectTorsion.defect_torsion | (intros; apply GlobalTheory.NL.DefectTorsion.defect_torsion <;> assumption)
