import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.HeightCounting.Up.ChebAtThird

theorem chebSplit_allSt : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL,
    AllSt fun _ _ _ _ _ _ x => ∀ _ : LC hL x, GlobalTheory.RowTie.ChebSplit (Dof x).nd := by
  intro hP hL
  exact StepW.of_all fun _ _ _ _ _ _ _ _ _ _ _ => GlobalTheory.ChebSplitDense.chebSplit_nd hP.what₂.cheb _

end GlobalTheory.HeightCounting.Up.ChebAtThird
