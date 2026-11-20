import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateKernelAtPoint
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_kernel_at_point : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint := by
  first | exact @GlobalTheory.HTKernel.hodgeTateKernelAtPoint | exact GlobalTheory.HTKernel.hodgeTateKernelAtPoint | (intros; apply GlobalTheory.HTKernel.hodgeTateKernelAtPoint <;> assumption)
