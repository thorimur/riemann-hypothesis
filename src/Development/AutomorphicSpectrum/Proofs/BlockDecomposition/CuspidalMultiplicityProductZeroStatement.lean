import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalMultiplicityProductZero
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_multiplicity_product_zero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ (ρ : IrrGL k) {h : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = ρ.1), ρ.IsCusp → 2 ≤ h → (∀ a, 0 < (x a).1) → jhMult ρ.rep (prodIrr x hd) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CuspNotInd.jhMult_eq_zero_of_isCusp | exact GlobalTheory.CompanionTheory.CuspNotInd.jhMult_eq_zero_of_isCusp | (intros; apply GlobalTheory.CompanionTheory.CuspNotInd.jhMult_eq_zero_of_isCusp <;> assumption)
