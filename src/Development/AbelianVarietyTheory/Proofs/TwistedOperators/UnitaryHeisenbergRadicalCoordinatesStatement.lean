import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryHeisenbergRadicalCoordinates
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_heisenberg_radical_coordinates : Heis := by
  first | exact @GlobalTheory.InertZeta.HeisCoord.Heisenberg₂ | exact GlobalTheory.InertZeta.HeisCoord.Heisenberg₂ | (intros; apply GlobalTheory.InertZeta.HeisCoord.Heisenberg₂ <;> assumption)
