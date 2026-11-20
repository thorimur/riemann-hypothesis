import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParameterLawsEmpty
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parameter_laws_empty : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, ∀ (D : D7) (cf : CharFrame D) rep Rw, IsEmpty D.nd.Loc → ParIn hL D cf rep Rw → ParLaws D := by
  first | exact @GlobalTheory.ParLawsBare.main | exact GlobalTheory.ParLawsBare.main | (intros; apply GlobalTheory.ParLawsBare.main <;> assumption)
