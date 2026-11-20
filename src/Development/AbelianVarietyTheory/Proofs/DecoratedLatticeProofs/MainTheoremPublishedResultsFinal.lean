import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonvanishingFromTruePackStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TruePackOfBundleStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MainTheoremFromPublishedResultsAltBis
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

theorem miStar_row : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → GlobalTheory.Published.DoublingMethod → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.StrongApproxSU → GlobalTheory.Core.Rk.RowDiag (fun D L C' => GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Bl.Prm hL), (∀ (K : Ctx) (q : Bl.WPt p.s K), Nonempty (Bl.RXs q.x.what₂)) → GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun _ _ _ _ b => PtRows b) → GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun _ _ _ _ b => (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE) := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hDiag hL p hRX hPt
  have hTrue : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun _ _ _ _ b => TruePack (packB b)) := by
    refine hPt.imp fun κ K β c b _ _ hl hP => ?_
    obtain ⟨q, b', ⟨w⟩, he⟩ := hl
    have key : ∀ s t : (Σ (D : D7) (O : Obj D), GlobalTheory.Fc.Bundle D O c), s = t →
        (PtRows t.2.2 → TruePack (packB t.2.2)) → PtRows s.2.2 → TruePack (packB s.2.2) := by
      rintro _ _ rfl h
      exact h
    exact key ⟨β.D, β.O, b⟩ ⟨q.w.D q.Z, q.O, b'⟩ he (fun hP' => GlobalTheory.T.true_pack_of_bundle q b' w (hRX K q) hP') hP
  have hPu := GlobalTheory.T.nonvanishing_from_true_pack hDiag hL p hTrue
  refine ((hPt.and hTrue).and hPu).imp fun κ K β c b _ _ _ H => ?_
  exact GlobalTheory.T.main_theorem_from_published_results_alt h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 (packB b) H.1.2 H.1.1.rS H.2

end GlobalTheory.Fam
