import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PositionStageMovesGeometric
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movable_geometric : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ) (Γ : GeoP), PositionMv (prmR (NEo hL cDep) SExt.none (geoCl Γ)).s := by
  first | exact @GlobalTheory.HeightCounting.Up.movable_prmR_nel | exact GlobalTheory.HeightCounting.Up.movable_prmR_nel | (intros; apply GlobalTheory.HeightCounting.Up.movable_prmR_nel <;> assumption)
