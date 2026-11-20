import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.Canon

theorem isRevOrdered_of_isCanon {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h : ℕ} (Γ : Fin h → Segment k) : IsCanon Γ → IsRevOrdered Γ :=
  fun hc i j hij hp => (hc.1 i j hij).1 hp.2

end GlobalTheory.CompanionTheory.Canon
