import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteFrameValuesStepZero
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelSite_frameValues_step_zero : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Law → S.Del 0) := by
  first | exact @GlobalTheory.TwV.StepZero.del_zero | exact GlobalTheory.TwV.StepZero.del_zero | (intros; apply GlobalTheory.TwV.StepZero.del_zero <;> assumption)
