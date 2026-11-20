import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroup
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraModules_indefiniteUnitaryGroup : GlobalTheory.Published.HarishChandraModules := by
  first | exact @GlobalTheory.HcPort.print_harishChandraModules | exact GlobalTheory.HcPort.print_harishChandraModules | (intros; apply GlobalTheory.HcPort.print_harishChandraModules <;> assumption)
