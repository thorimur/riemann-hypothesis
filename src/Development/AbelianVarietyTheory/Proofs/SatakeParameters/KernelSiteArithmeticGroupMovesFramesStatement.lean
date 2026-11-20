import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteArithmeticGroupMovesFrames
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelSite_arithmeticGroup_moves_frames : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Move) := by
  first | exact @GlobalTheory.TwV.move_at_site | exact GlobalTheory.TwV.move_at_site | (intros; apply GlobalTheory.TwV.move_at_site <;> assumption)
