import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLatticePeriodicity
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_periodicity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] (φ : (Fin t → k) → Z), IsLocallyConstant φ → HasCompactSupport φ → ∃ c : k, c ≠ 0 ∧ ∀ o ∈ Lc t c, ∀ v, φ (v + o.toAdd) = φ v := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.LatInv.exists_Lc_invariant | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.LatInv.exists_Lc_invariant | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.LatInv.exists_Lc_invariant <;> assumption)
