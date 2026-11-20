import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmallPairPairingAllGluedPlacesProof
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallPairPairingAllGluedPlaces_proof : ∀ D : D7, GlobalTheory.FinPl.SmallAll D := by
  first | exact @GlobalTheory.FinPl.SmallAllPf.main | exact GlobalTheory.FinPl.SmallAllPf.main | (intros; apply GlobalTheory.FinPl.SmallAllPf.main <;> assumption)
