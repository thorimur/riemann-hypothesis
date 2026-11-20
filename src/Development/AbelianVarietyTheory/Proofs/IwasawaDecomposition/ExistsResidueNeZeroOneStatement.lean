import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsResidueNeZeroOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_residue_ne_zero_one : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t _ _ c =>
  ∀ PP ∈ t.r.z.R.Pg, ∃ x : Formalism.L2.DIV.kP PP, x ≠ 0 ∧ x ≠ 1 := by
  first | exact @GlobalTheory.ResThree.main | exact GlobalTheory.ResThree.main | (intros; apply GlobalTheory.ResThree.main <;> assumption)
