import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralRationalAtMember
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_rational_at_member : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ _ _ _ _ t _ _ _ => GlobalTheory.CenLocAt.CenRat t.r.Y t.r.z.cG := by
  first | exact @GlobalTheory.CenRatAt.cenRat_at | exact GlobalTheory.CenRatAt.cenRat_at | (intros; apply GlobalTheory.CenRatAt.cenRat_at <;> assumption)
