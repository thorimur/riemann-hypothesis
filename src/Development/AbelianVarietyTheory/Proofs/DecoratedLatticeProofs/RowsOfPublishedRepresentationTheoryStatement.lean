import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowsOfRepresentationTheoryOfHyp
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rows_of_published_representation_theory : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Bl.Prm hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun _ _ _ _ b => PtRows b) := by
  first | exact @GlobalTheory.Fam.PtRowsAt.ptRows_at_member | exact GlobalTheory.Fam.PtRowsAt.ptRows_at_member | (intros; apply GlobalTheory.Fam.PtRowsAt.ptRows_at_member <;> assumption)
