import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MainTheoremPublishedResultsFinalStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowsOfPublishedRepresentationTheoryStatement
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem miStarRowClosing : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → GlobalTheory.Published.DoublingMethod → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.StrongApproxSU → GlobalTheory.Core.Rk.RowDiag (fun D L C' => GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Bl.Prm hL), (∀ (K : Ctx) (q : Bl.WPt p.s K), Nonempty (Bl.RXs q.x.what₂)) → GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun _ _ _ _ b => (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE) := by
  intro hHCF hCusp hDSC hHCM hCW hHowe hWeil hWSF hSWC hDbl hUDG hDSCl hSA hDiag hL p hRX
  exact GlobalTheory.T.main_theorem_published_results_final hHCF hCusp hDSC hHCM hCW hHowe hWeil hWSF hSWC hDbl hUDG hDSCl hSA hDiag hL p hRX
    (GlobalTheory.T.rows_of_published_representation_theory hDSC hHCM hCW hHCF hCusp hL p)

end GlobalTheory
