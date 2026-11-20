import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SeriesLocationOfMembership
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.series_location_of_membership : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ _ _ _ _ => GlobalTheory.TypeLeaf.SerLoc (w.D Z) := by
  first | exact @GlobalTheory.SerFinished.main | exact GlobalTheory.SerFinished.main | (intros; apply GlobalTheory.SerFinished.main <;> assumption)
