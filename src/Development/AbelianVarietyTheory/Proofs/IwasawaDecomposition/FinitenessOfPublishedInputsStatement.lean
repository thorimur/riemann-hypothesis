import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitenessOfHyp
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteness_of_localLanglands : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, ArchCmp hL → SEta hL → SXd hL → SFin hL ∧ ∀ cDep : ℝ, SFinl hL cDep := by
  first | exact @GlobalTheory.HeightCounting.Fin3.sFin | exact GlobalTheory.HeightCounting.Fin3.sFin | (intros; apply GlobalTheory.HeightCounting.Fin3.sFin <;> assumption)
