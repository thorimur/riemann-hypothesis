import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DoublingInputsImply
open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.LiteralAutomorphy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubling_inputs_imply : PrM → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitarySchrodinger → GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.SiegelEisensteinSimplePole → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.SchurOrthogonalitySquareIntegrable → GlobalTheory.Published.RegularisedSiegelWeilFirstTerm → RowRatW → HypH := by
  first | exact @GlobalTheory.Mem.hypH_of_rowRatW | exact GlobalTheory.Mem.hypH_of_rowRatW | (intros; apply GlobalTheory.Mem.hypH_of_rowRatW <;> assumption)
