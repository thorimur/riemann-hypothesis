import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceShiftOfDieudonne
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.place_shift_of_dieudonne : GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.Published.PrismaticDieudonneHodge → GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint → GlobalTheory.FlatCM.PlaceShiftSt := by
  first | exact @GlobalTheory.PlaceShiftGlue.placeShift | exact GlobalTheory.PlaceShiftGlue.placeShift | (intros; apply GlobalTheory.PlaceShiftGlue.placeShift <;> assumption)
