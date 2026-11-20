import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WitnessesPassAlongSetDivision
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witnesses_pass_along_set_division : ∀ 𝒮 : Slots, PositionMv 𝒮 → WitMv 𝒮 := by
  first | exact @GlobalTheory.Mem.Top.Bl.witMv_of_positionMv | exact GlobalTheory.Mem.Top.Bl.witMv_of_positionMv | (intros; apply GlobalTheory.Mem.Top.Bl.witMv_of_positionMv <;> assumption)
