import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodFiberTypesAll
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_fiber_types_all : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ _ _ _ _ _ x => LA hL x → GoodFTAll (Dof x) := by
  first | exact @GlobalTheory.GoodFirst.goodFTAll_allSt | exact GlobalTheory.GoodFirst.goodFTAll_allSt | (intros; apply GlobalTheory.GoodFirst.goodFTAll_allSt <;> assumption)
