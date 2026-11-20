import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilRepresentationRulesHold
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentationRules_hold : ∀ D : D7, WeilRules D := by
  first | exact @GlobalTheory.Mem.WeilRule.weilRules | exact GlobalTheory.Mem.WeilRule.weilRules | (intros; apply GlobalTheory.Mem.WeilRule.weilRules <;> assumption)
