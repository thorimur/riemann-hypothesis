import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspidalModerateGrowthRapidDecay
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_moderateGrowth_rapidDecay : GlobalTheory.Published.CuspDecayBound := by
  first | exact @GlobalTheory.CuspGeo.cuspDecayBound | exact GlobalTheory.CuspGeo.cuspDecayBound | (intros; apply GlobalTheory.CuspGeo.cuspDecayBound <;> assumption)
