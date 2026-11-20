import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsInjectiveOfSocle
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlands_injective_of_socle : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), LSocleGL k → LSegJacquet k → LInjective k := by
  first | exact @GlobalTheory.CompanionTheory.Multisegment.lInjective | exact GlobalTheory.CompanionTheory.Multisegment.lInjective | (intros; apply GlobalTheory.CompanionTheory.Multisegment.lInjective <;> assumption)
