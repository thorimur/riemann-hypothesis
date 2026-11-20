import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceShiftOfDieudonneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateKernelAtPointStatement
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory

namespace GlobalTheory

theorem placeShiftSt_of_scholzeWeinstein (hP : GlobalTheory.CovTop.Hypotheses2) (hSW : GlobalTheory.Published.ScholzeWeinsteinB) :
    GlobalTheory.FlatCM.PlaceShiftSt :=
  GlobalTheory.T.place_shift_of_dieudonne hSW hP.q4 (GlobalTheory.T.hodge_tate_kernel_at_point hP)

end GlobalTheory
