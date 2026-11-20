import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentTermInjective
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_term_injective : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k), Function.Injective Δ.term := by
  first | exact @GlobalTheory.CompanionTheory.SegTerm.term_injective | exact GlobalTheory.CompanionTheory.SegTerm.term_injective | (intros; apply GlobalTheory.CompanionTheory.SegTerm.term_injective <;> assumption)
