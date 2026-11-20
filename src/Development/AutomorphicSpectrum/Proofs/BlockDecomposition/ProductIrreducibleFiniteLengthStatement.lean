import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_irreducible_finite_length : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), HasFiniteLength (prodIrr x hd) := by
  first | exact @GlobalTheory.CompanionTheory.ProdFL.main | exact GlobalTheory.CompanionTheory.ProdFL.main | (intros; apply GlobalTheory.CompanionTheory.ProdFL.main <;> assumption)
