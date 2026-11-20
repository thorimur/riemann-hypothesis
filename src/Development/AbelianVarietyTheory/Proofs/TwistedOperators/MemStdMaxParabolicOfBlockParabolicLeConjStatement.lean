import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemStdMaxParabolicOfBlockParabolicLeConj

open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_stdMaxParabolic_of_blockParabolic_le_conj : ∀ (F : Type) [Field F] {r a b s : ℕ} (h : a + b = r) (d : Fin s → ℕ) (hd : ∑ i, d i = r) (g : GL (Fin r) F),
    parab F (stdBlocks d hd) ≤ conjBy g (stdMaxParab F h) → g ∈ stdMaxParab F h := by
  first | exact @GlobalTheory.ParabConj.mem_stdMaxParab_of_le_conjBy | exact GlobalTheory.ParabConj.mem_stdMaxParab_of_le_conjBy | (intros; apply GlobalTheory.ParabConj.mem_stdMaxParab_of_le_conjBy <;> assumption)
