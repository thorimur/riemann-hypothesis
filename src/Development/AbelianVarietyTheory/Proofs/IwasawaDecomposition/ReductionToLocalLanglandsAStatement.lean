import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionToLocalLanglandsA
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_to_local_langlands_A : PrN → PhtCmp → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, SA hL := by
  first | exact @GlobalTheory.HeightCounting.Up.sa_of_prN | exact GlobalTheory.HeightCounting.Up.sa_of_prN | (intros; apply GlobalTheory.HeightCounting.Up.sa_of_prN <;> assumption)
