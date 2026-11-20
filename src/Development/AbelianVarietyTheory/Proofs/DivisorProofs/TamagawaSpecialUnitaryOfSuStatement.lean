import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamagawaSpecialUnitaryOfSu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tamagawa_special_unitary_of_su : GlobalTheory.Published.TamagawaNumberSU → GlobalTheory.Published.TamagawaSpecialUnitary := by
  first | exact @GlobalTheory.TamUnfoldSU.tamagawaSpecialUnitary | exact GlobalTheory.TamUnfoldSU.tamagawaSpecialUnitary | (intros; apply GlobalTheory.TamUnfoldSU.tamagawaSpecialUnitary <;> assumption)
